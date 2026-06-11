

(*  Part 1 *)
type value =
  | Int of int
  | Bool of bool
  | Str of string
  | Name of string
  | Unit
  | Error

(*  This is where the stack defined with the type it accepts *)
type stack = value list ref

exception Quit
exception ErrorMsg of string

let empty_stack () = ref []

let push (stk : stack) (v : value) : unit =
  stk := v :: !stk

let pop (stk : stack) : value option =
  match !stk with
  | [] -> None
  | x :: xs -> stk := xs; Some x

(* Helper function for part 1 *)
let stringOfVal = function
  | Int n -> string_of_int n
  | Bool true -> ":true:"
  | Bool false -> ":false:"
  | Str s -> s
  | Name n -> n
  | Unit -> ":unit:"
  | Error -> ":error:"

(* Arithmetic Operators (Part 1) *)
(* 4.6 addition *)
let add stk =
  match !stk with
  | Int a :: Int b :: rest -> stk := Int (b + a) :: rest
  | x :: y :: rest -> stk := y :: x :: Error :: rest
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [Error]

(* 4.7 subtraction *)
let sub stk =
  match !stk with
  | Int a :: Int b :: rest -> stk := Int (b - a) :: rest
  | x :: y :: rest -> stk := y :: x :: Error :: rest
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [Error]

(* 4.8 multiplication *)
let mult stk =
  match !stk with
  | Int a :: Int b :: rest -> stk := Int (b * a) :: rest
  | x :: y :: rest -> stk := y :: x :: Error :: rest
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [Error]

(* 4.9 division *)
let div stk =
  match !stk with
  | Int 0 :: Int _ :: _ -> stk := Error :: !stk
  | Int a :: Int b :: rest -> stk := Int (b / a) :: rest
  | x :: y :: rest -> stk := y :: x :: Error :: rest
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [Error]

(* 4.10 remainder *)
let rem stk =
  match !stk with
  | Int 0 :: Int _ :: _ -> stk := Error :: !stk
  | Int a :: Int b :: rest -> stk := Int (b mod a) :: rest
  | x :: y :: rest -> stk := y :: x :: Error :: rest
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [Error]

(* 4.11 sign *)
let sign stk =
  match !stk with
  | Int n :: rest -> stk := Int (-n) :: rest
  | x :: rest -> stk := x :: Error :: rest
  | [] -> stk := [Error]

(* 4.12 swap *)
let swap stk =
  match !stk with
  | a :: b :: rest -> stk := b :: a :: rest
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [Error]

(* 4.13 toString *)
let toString stk =
  match !stk with
  | v :: rest -> stk := Str (stringOfVal v) :: rest
  | [] -> stk := [Error]

(* 4.14 print line *)
let println stk oc =
  match !stk with
  | [] -> stk := [Error]
  | v :: rest ->
      stk := rest;
      Printf.fprintf oc "%s\n" (stringOfVal v)

(* parsing (parts 4.1–4.4) *)
let parse_constant (s : string) : value =
  let s = String.trim s in

  (* 4.3 push bool *)
  if s = ":true:" then Bool true
  else if s = ":false:" then Bool false

  (* 4.4 push :error:, :unit: *)
  else if s = ":unit:" then Unit
  else if s = ":error:" then Error

  (* 4.1 push string *)
  else if String.length s >= 2 && s.[0] = '"' && s.[String.length s - 1] = '"' then
    Str (String.sub s 1 (String.length s - 2))

  (* 4.1 push int + 4.2 push name *)
  else
    try Int (int_of_string s)
    with Failure _ ->
      let valid_name_start c =
        Char.(c = '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'))
      in
      let valid_name_char c =
        Char.(c = '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9'))
      in
      if String.length s > 0 && valid_name_start s.[0]
         && (let rec ok i =
               if i >= String.length s then true
               else valid_name_char s.[i] && ok (i+1)
             in ok 1)
      then Name s
      else Error

(* PART 2 *)
(* environments and scopes *)
(* env = stack of scopes . Each scope is name * value *)
type env = (string * value) list list ref
let empty_env () : env = ref [ [] ]
let push_scope (e : env) : unit = e := [] :: !e
let pop_scope  (e : env) : unit =
  match !e with
  | [] | [_] -> ()
  | _ :: rest -> e := rest

(* lookup name from current scope outward *)
let rec env_lookup (e : env) (x : string) : value option =
  let rec findScope scope =
    match scope with
    | [] -> None
    | (k, v) :: tl -> if String.equal k x then Some v else findScope tl
  in
  let rec go scopes =
    match scopes with
    | [] -> None
    | s :: tl -> (match findScope s with Some v -> Some v | None -> go tl)
  in
  go !e

(* bind in current scope so replace if it exists and if doesn't add *)
let env_bind (e : env) (x : string) (v : value) : unit =
  match !e with
  | [] -> e := [ [ (x, v) ] ]
  | scope :: rest ->
      let rec replace acc = function
        | [] -> List.rev ((x, v) :: acc)
        | (k, _ as kv) :: tl ->
            if String.equal k x then List.rev_append acc ((x, v) :: tl)
            else replace (kv :: acc) tl
      in
      let new_scope =
        if List.exists (fun (k, _) -> String.equal k x) scope
        then replace [] scope
        else (x, v) :: scope
      in
      e := new_scope :: rest

(* resolve a value if it is a name, following chains of bindings *)
let rec resolve (e : env) (v : value) : value =
  match v with
  | Name x ->
      (match env_lookup e x with
       | None -> Error
       | Some v' ->
           (match v' with Name _ -> resolve e v' | _ -> v'))
  | _ -> v

(* pop N while preserving original order *)
let pop2 (stk : stack) : (value * value) option =
  match !stk with
  | a :: b :: tl -> stk := tl; Some (a, b)
  | _ -> None

let push_restore2 (stk : stack) (a : value) (b : value) : unit =
  (* restore original order (top first), then push :error: on top *)
  stk := a :: b :: !stk;
  stk := Error :: !stk

(* Part 2 *)

(* 5.1 concatenation *)
let cat stk =
  match pop2 stk with
  | Some (x, y) ->
      let sx, sy =
        match (x, y) with
        | (Str s1, Str s2) -> Some s1, Some s2
        | _ -> None, None
      in
      (match (sx, sy) with
       | (Some s1, Some s2) -> push stk (Str (stringOfVal y ^ stringOfVal x)) (* y ^ x *)
       | _ -> push_restore2 stk x y)
  | None ->
      (match !stk with
       | a :: _ -> stk := Error :: !stk
       | [] -> stk := [Error])

(* 5.2 and - conjunction *)
let land_cmd (stk : stack) (env : env) =
  match pop2 stk with
  | Some (x, y) ->
      let vx = resolve env x and vy = resolve env y in
      (match (vx, vy) with
       | (Bool b1, Bool b2) -> push stk (Bool (b2 && b1))
       | _ -> push_restore2 stk x y)
  | None -> stk := Error :: !stk

(* 5.3 or - disjunction *)
let lor_cmd (stk : stack) (env : env) =
  match pop2 stk with
  | Some (x, y) ->
      let vx = resolve env x and vy = resolve env y in
      (match (vx, vy) with
       | (Bool b1, Bool b2) -> push stk (Bool (b2 || b1))
       | _ -> push_restore2 stk x y)
  | None -> stk := Error :: !stk

(* 5.4 not - negation *)
let lnot_cmd (stk : stack) (env : env) =
  match pop stk with
  | Some x ->
      (match resolve env x with
       | Bool b -> push stk (Bool (not b))
       | _ -> push stk x; push stk Error)
  | None -> stk := [Error]

(* 5.5 equal *)
let equal_cmd (stk : stack) (env : env) =
  match pop2 stk with
  | Some (x, y) ->
      let vx = resolve env x and vy = resolve env y in
      (match (vx, vy) with
       | (Int a, Int b) -> push stk (Bool (b = a))
       | _ -> push_restore2 stk x y)
  | None -> stk := Error :: !stk

(* 5.6 lessThan *)
let lt_cmd (stk : stack) (env : env) =
  match pop2 stk with
  | Some (x, y) ->
      let vx = resolve env x and vy = resolve env y in
      (match (vx, vy) with
       | (Int a, Int b) -> push stk (Bool (b < a))
       | _ -> push_restore2 stk x y)
  | None -> stk := Error :: !stk

(* 5.7 assign *)
let assign_cmd (stk : stack) (env : env) =
  match pop2 stk with
  | Some (v, n) ->
      (match n with
       | Name id ->
           let rv = resolve env v in
           (match rv with
            | Error -> push_restore2 stk v n
            | _ ->
                env_bind env id rv;
                push stk Unit)
       | _ -> push_restore2 stk v n)
  | None -> stk := Error :: !stk

(* 5.10 if *)
let if_cmd (stk : stack) (env : env) =
  (* pops x, y, z (z must be boolean); if z then push x else push y *)
  match pop stk with
  | Some x ->
      (match pop stk with
       | Some y ->
           (match pop stk with
            | Some z ->
                (match resolve env z with
                 | Bool true -> push stk x
                 | Bool false -> push stk y
                 | _ ->
                     (* restore x y z in order, then :error: *)
                     push stk z; push stk y; push stk x; push stk Error)
            | None -> push stk y; push stk x; stk := Error :: !stk)
       | None -> push stk x; stk := Error :: !stk)
  | None -> stk := [Error]

(* 5.11 let...end *)
(* We add stack *frames* and env scopes.
   - 'let'  : push a new empty stack frame and a new env scope.
   - 'end'  : pop inner frame, take its top value (must exist), push onto outer frame; pop env scope. *)

(* stack frame stack (top = current) *)
let frames : (value list ref) list ref = ref []

let begin_frames (initial : stack) =
  if !frames = [] then frames := [ initial ] else ()

let current_frame () : stack =
  match !frames with
  | [] -> failwith "no frame"
  | fr :: _ -> fr

let push_frame () =
  frames := (ref []) :: !frames

let pop_frame_and_return_to_outer () : unit =
  match !frames with
  | [] | [ _ ] -> ()   (* cannot pop the only/global frame *)
  | inner :: outer :: rest ->
      (* take top of inner; spec guarantees at least 1 item after let...end *)
      (match !inner with
       | v :: _ ->
           (* drop inner frame; restore outer as current, push v there *)
           frames := outer :: rest;
           push outer v
       | [] ->
           (* if empty, push :error: to outer *)
           frames := outer :: rest;
           push outer Error)

let handle_let (_stk : stack) (env : env) =
  (* push new scope + new frame; switch current stack to that frame *)
  push_scope env;
  push_frame ()

let handle_end (_stk : stack) (env : env) =
  (* pop scope, pop frame and push its top onto the outer frame *)
  pop_scope env;
  pop_frame_and_return_to_outer ()

(* Command Execution (Part 1 + Part 2) *)

let execute_command (stk : stack) (env : env) (line : string) (oc : out_channel) =
  let parts = String.split_on_char ' ' (String.trim line) |> List.filter (fun s -> s <> "") in
  match parts with
  | [] -> ()
  (* 4.15 quit  *)
  | ["quit"] -> raise Quit

  (* 4.5 pop *)
  | ["pop"] -> (match pop stk with Some _ -> () | None -> push stk Error)
  | ["add"] -> add stk
  | ["sub"] -> sub stk
  | ["mult"] -> mult stk
  | ["div"] -> div stk
  | ["rem"] -> rem stk
  | ["sign"] -> sign stk
  | ["swap"] -> swap stk
  | ["toString"] -> toString stk
  | ["println"] -> println stk oc

  (* 5.1 cat *)
  | ["cat"] -> cat stk

  (* 5.2 and *)
  | ["and"] -> land_cmd stk env

  (* 5.3 or *)
  | ["or"] -> lor_cmd stk env

  (* 5.4 not *)
  | ["not"] -> lnot_cmd stk env

  (* 5.5 equal *)
  | ["equal"] -> equal_cmd stk env

  (* 5.6 lessThan *)
  | ["lessThan"] -> lt_cmd stk env

  (* 5.7 assign *)
  | ["assign"] -> assign_cmd stk env

  (* 5.10 if *)
  | ["if"] -> if_cmd stk env

  (* 5.11 let...end *)
  | ["let"] -> handle_let stk env
  | ["end"] -> handle_end stk env

  (* 4.1 push *)
  | ["push"; _const] ->
      let arg = String.sub line 5 (String.length line - 5) |> String.trim in
      let value = parse_constant arg in
      push stk value
  | _ -> push stk Error


(* file reading and main loop *)
let interpreter ((input, output) : string * string) : unit =
  let ic = open_in input in
  let oc = open_out output in
  let stk = empty_stack () in
  let env = empty_env () in
  begin_frames stk;
  (try
     while true do
       let line = input_line ic in
       if String.trim line <> "" then
         execute_command (current_frame ()) env line oc
     done
   with
   | End_of_file -> ()
   | Quit -> ());
  close_in ic;
  close_out oc
;;
(* to test output *)
   interpreter ("input.txt", "output.txt")