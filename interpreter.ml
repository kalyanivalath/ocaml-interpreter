(* 
Language Interpreter Project

Authors: Kalyani Valath and Aidan Williams

Course: CS 3323

Part 1:
This part handles ints, bools, strings, and names 
on a stack and supports arithmetic, stack operations, printing.

Part 2:
This part adds an environment with variables and scopes. It binds names with assign, 
use let/end blocks, boolean operations, if, and string operations like cat.

Part 3:
This part adds functions and closures and will also handle floats now. 
It supports fun/inOutFun definitions, call and return, and keeps track of environments 
so functions know where they were defined. inOutFun also updates the caller’s variable.
*)

(* values that are part of stack/env *)
type value =
  | Int of int
  | Float of float
  | Bool of bool
  | Str of string
  | Name of string
  | Unit
  | Error
  | Closure of closure

(* function closures store the func name, param, body, and env *)
and closure = {
  func_name: string;
  param_name: string;
  body: string list;
  env_snapshot: env;
  is_inout: bool;
}

(* environment is a stack of scopes *)
and env = (string * value) list list ref

(* stack is just a list of values *)
type stack = value list ref

exception Quit

(* create an empty stack *)
let empty_stack () = ref []

(* push value onto stack *)
let push (stk : stack) (v : value) : unit =
  stk := v :: !stk

(* pop value from stack *)
let pop (stk : stack) : value option =
  match !stk with
  | [] -> None
  | x :: xs -> stk := xs; Some x

(* turn value into string *)
let stringOfVal = function
  | Int n -> string_of_int n
  | Float f ->
      let s = string_of_float f in
      if String.length s >= 2 && String.sub s (String.length s - 2) 2 = ".0" then
        String.sub s 0 (String.length s - 2)
      else if String.get s (String.length s - 1) = '.' then
        String.sub s 0 (String.length s - 1)
      else
        s
  | Bool true -> ":true:"
  | Bool false -> ":false:"
  | Str s -> s
  | Name n -> n
  | Unit -> ":unit:"
  | Error -> ":error:"
  | Closure _ -> ":fun:"

(* parse a constant from the input *)
let parse_constant (s : string) : value =
  let s = String.trim s in
  if s = ":true:" then Bool true
  else if s = ":false:" then Bool false
  else if s = ":unit:" then Unit
  else if s = ":error:" then Error
  else if String.length s >= 2 && s.[0] = '"' && s.[String.length s - 1] = '"' then
    Str (String.sub s 1 (String.length s - 2))
  else
    try
      Int (int_of_string s)
    with Failure _ ->
      (try
         let f = float_of_string s in
         if String.contains s '.' then Float f else Error
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
         else Error)

(* environment helpers *)
let empty_env () : env = ref [ [] ]

let push_scope (env : env) : unit =
  env := [] :: !env

let pop_scope (env : env) : unit =
  match !env with
  | [] | [_] -> ()
  | _ :: rest -> env := rest

let rec env_lookup (env : env) (x : string) : value option =
  let rec find_in_scope scope =
    match scope with
    | [] -> None
    | (k, v) :: tl ->
        if String.equal k x then Some v else find_in_scope tl
  in
  let rec search scopes =
    match scopes with
    | [] -> None
    | scope :: rest ->
        (match find_in_scope scope with
         | Some v -> Some v
         | None -> search rest)
  in
  search !env

let env_bind (env : env) (x : string) (v : value) : unit =
  match !env with
  | [] -> env := [ [ (x, v) ] ]
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
      env := new_scope :: rest

(* resolve name to its final value using the environment *)
let rec resolve (env : env) (v : value) : value =
  match v with
  | Name x ->
      (match env_lookup env x with
       | None -> Error
       | Some v' ->
           (match v' with
            | Name _ -> resolve env v'
            | _ -> v'))
  | _ -> v

(* Arithmetic operations for part 1 and 3 because now it will handle floats as well *)
let add stk env =
  match !stk with
  | a :: b :: rest ->
      let ra = resolve env a in
      let rb = resolve env b in
      (match (ra, rb) with
       | Int ia, Int ib -> stk := Int (ib + ia) :: rest
       | Float fa, Float fb -> stk := Float (fb +. fa) :: rest
       | Float fa, Int ib -> stk := Float (float_of_int ib +. fa) :: rest
       | Int ia, Float fb -> stk := Float (fb +. float_of_int ia) :: rest
       | _ ->
           stk := rest;
           push stk b;
           push stk a;
           push stk Error)
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [ Error ]

let sub stk env =
  match !stk with
  | a :: b :: rest ->
      let ra = resolve env a in
      let rb = resolve env b in
      (match (ra, rb) with
       | Int ia, Int ib -> stk := Int (ib - ia) :: rest
       | Float fa, Float fb -> stk := Float (fb -. fa) :: rest
       | Float fa, Int ib -> stk := Float (float_of_int ib -. fa) :: rest
       | Int ia, Float fb -> stk := Float (fb -. float_of_int ia) :: rest
       | _ ->
           stk := rest;
           push stk b;
           push stk a;
           push stk Error)
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [ Error ]

let mult stk env =
  match !stk with
  | a :: b :: rest ->
      let ra = resolve env a in
      let rb = resolve env b in
      (match (ra, rb) with
       | Int ia, Int ib -> stk := Int (ib * ia) :: rest
       | Float fa, Float fb -> stk := Float (fb *. fa) :: rest
       | Float fa, Int ib -> stk := Float (float_of_int ib *. fa) :: rest
       | Int ia, Float fb -> stk := Float (fb *. float_of_int ia) :: rest
       | _ ->
           stk := rest;
           push stk b;
           push stk a;
           push stk Error)
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [ Error ]

let div stk env =
  match !stk with
  | a :: b :: rest ->
      let ra = resolve env a in
      let rb = resolve env b in
      (match (ra, rb) with
       | Int 0, Int _ -> stk := Error :: !stk
       | Int ia, Int ib -> stk := Int (ib / ia) :: rest
       | Float fa, Float fb when fa = 0.0 -> stk := Error :: !stk
       | Float fa, Float fb -> stk := Float (fb /. fa) :: rest
       | Float fa, Int ib when fa = 0.0 -> stk := Error :: !stk
       | Float fa, Int ib -> stk := Float (float_of_int ib /. fa) :: rest
       | Int ia, Float fb when float_of_int ia = 0.0 -> stk := Error :: !stk
       | Int ia, Float fb -> stk := Float (fb /. float_of_int ia) :: rest
       | _ ->
           stk := rest;
           push stk b;
           push stk a;
           push stk Error)
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [ Error ]

let rem stk env =
  match !stk with
  | a :: b :: rest ->
      let ra = resolve env a in
      let rb = resolve env b in
      (match (ra, rb) with
       | Int 0, Int _ -> stk := Error :: !stk
       | Int ia, Int ib -> stk := Int (ib mod ia) :: rest
       | _ ->
           stk := rest;
           push stk b;
           push stk a;
           push stk Error)
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [ Error ]

let sign stk env =
  match !stk with
  | x :: rest ->
      let rx = resolve env x in
      (match rx with
       | Int n -> stk := Int (-n) :: rest
       | Float f -> stk := Float (-. f) :: rest
       | _ -> stk := x :: Error :: rest)
  | [] -> stk := [ Error ]

let swap stk =
  match !stk with
  | a :: b :: rest -> stk := b :: a :: rest
  | [ _ ] -> stk := Error :: !stk
  | [] -> stk := [ Error ]

let toString stk =
  match !stk with
  | v :: rest -> stk := Str (stringOfVal v) :: rest
  | [] -> stk := [ Error ]

let println stk oc =
  match !stk with
  | [] -> stk := [ Error ]
  | v :: rest ->
      stk := rest;
      Printf.fprintf oc "%s\n" (stringOfVal v)

(* helpers for two-value pops *)
let pop2 (stk : stack) : (value * value) option =
  match !stk with
  | a :: b :: tl ->
      stk := tl;
      Some (a, b)
  | _ -> None

let push_restore2 (stk : stack) (a : value) (b : value) : unit =
  stk := a :: b :: !stk;
  stk := Error :: !stk

(* Part 2 operations *)
let cat stk =
  match pop2 stk with
  | Some (x, y) ->
      let sx, sy =
        match (x, y) with
        | Str s1, Str s2 -> Some s1, Some s2
        | _ -> None, None
      in
      (match sx, sy with
       | Some _, Some _ -> push stk (Str (stringOfVal y ^ stringOfVal x))
       | _ -> push_restore2 stk x y)
  | None ->
      (match !stk with
       | _ :: _ -> stk := Error :: !stk
       | [] -> stk := [ Error ])

let land_cmd (stk : stack) (env : env) =
  match pop2 stk with
  | Some (x, y) ->
      let vx = resolve env x in
      let vy = resolve env y in
      (match vx, vy with
       | Bool b1, Bool b2 -> push stk (Bool (b2 && b1))
       | _ -> push_restore2 stk x y)
  | None -> stk := Error :: !stk

let lor_cmd (stk : stack) (env : env) =
  match pop2 stk with
  | Some (x, y) ->
      let vx = resolve env x in
      let vy = resolve env y in
      (match vx, vy with
       | Bool b1, Bool b2 -> push stk (Bool (b2 || b1))
       | _ -> push_restore2 stk x y)
  | None -> stk := Error :: !stk

let lnot_cmd (stk : stack) (env : env) =
  match pop stk with
  | Some x ->
      (match resolve env x with
       | Bool b -> push stk (Bool (not b))
       | _ ->
           push stk x;
           push stk Error)
  | None -> stk := [ Error ]

let equal_cmd (stk : stack) (env : env) =
  match pop2 stk with
  | Some (x, y) ->
      let vx = resolve env x in
      let vy = resolve env y in
      (match vx, vy with
       | Int a, Int b -> push stk (Bool (b = a))
       | Float a, Float b -> push stk (Bool (b = a))
       | Int a, Float b -> push stk (Bool (b = float_of_int a))
       | Float a, Int b -> push stk (Bool (float_of_int b = a))
       | _ -> push_restore2 stk x y)
  | None -> stk := Error :: !stk

let lt_cmd (stk : stack) (env : env) =
  match pop2 stk with
  | Some (x, y) ->
      let vx = resolve env x in
      let vy = resolve env y in
      (match vx, vy with
       | Int a, Int b -> push stk (Bool (b < a))
       | Float a, Float b -> push stk (Bool (b < a))
       | _ -> push_restore2 stk x y)
  | None -> stk := Error :: !stk

let assign_cmd (stk : stack) (env : env) =
  match pop2 stk with
  | Some (value, name_or_error) ->
      (match name_or_error with
       | Name id ->
           let rv = resolve env value in
           (match rv with
            | Error -> push_restore2 stk value name_or_error
            | Closure _ -> push_restore2 stk value name_or_error
            | _ ->
                env_bind env id rv;
                push stk Unit)
       | _ -> push_restore2 stk value name_or_error)
  | None -> stk := Error :: !stk

let if_cmd (stk : stack) (env : env) =
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
                     push stk z;
                     push stk y;
                     push stk x;
                     push stk Error)
            | None ->
                push stk y;
                push stk x;
                stk := Error :: !stk)
       | None ->
           push stk x;
           stk := Error :: !stk)
  | None -> stk := [ Error ]

(* stack frames for let/end *)
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
  | [] | [ _ ] -> ()
  | inner :: outer :: rest ->
      let inner_vals = !inner in
      frames := outer :: rest;
      List.iter (fun v -> push outer v) (List.rev inner_vals)

let handle_let (_stk : stack) (env : env) =
  push_scope env;
  push_frame ()

let handle_end (_stk : stack) (env : env) =
  pop_scope env;
  pop_frame_and_return_to_outer ()

(* Part 3 *)
let saved_stacks : (value list ref) list ref = ref []
let saved_envs : env list ref = ref []
let return_triggered = ref false

let copy_env (env : env) : env =
  ref (List.map (fun scope -> List.map (fun (k, v) -> (k, v)) scope) !env)

let rec execute_commands_list (commands : string list) (stk : stack) (env : env) (oc : out_channel) :
    unit =
  match commands with
  | [] -> ()
  | cmd :: rest ->
      if !return_triggered then ()
      else begin
        execute_command stk env cmd oc;
        if not !return_triggered then
          execute_commands_list rest stk env oc
      end

and handle_call (stk : stack) (env : env) (oc : out_channel) : unit =
  match pop stk with
  | Some arg_val ->
      (match pop stk with
       | Some func_val ->
           let resolved_func = resolve env func_val in
           (match resolved_func with
            | Closure clos ->
                let resolved_arg = resolve env arg_val in
                (match resolved_arg with
                 | Error ->
                     push stk func_val;
                     push stk arg_val;
                     push stk Error
                 | _ ->
                     saved_stacks := (ref !stk) :: !saved_stacks;
                     saved_envs := (copy_env env) :: !saved_envs;
                     env := !(clos.env_snapshot);
                     env_bind env clos.param_name resolved_arg;
                     stk := [];
                     return_triggered := false;
                     execute_commands_list clos.body stk env oc;
                     let return_val =
                       match !stk with
                       | v :: _ -> v
                       | [] -> Unit
                     in
                     let final_param_val =
                       if clos.is_inout then
                         match env_lookup env clos.param_name with
                         | Some v -> v
                         | None -> resolved_arg
                       else resolved_arg
                     in
                     (match !saved_stacks, !saved_envs with
                      | old_stk :: stk_rest, old_env :: env_rest ->
                          saved_stacks := stk_rest;
                          saved_envs := env_rest;
                          stk := !old_stk;
                          env := !old_env;
                          if clos.is_inout then
                            (match arg_val with
                             | Name n -> env_bind env n final_param_val
                             | _ -> ());
                          push stk return_val;
                          return_triggered := false
                      | _ -> ()))
            | _ ->
                push stk func_val;
                push stk arg_val;
                push stk Error)
       | None ->
           push stk arg_val;
           push stk Error)
  | None -> push stk Error

and handle_return () : unit =
  return_triggered := true

and execute_command (stk : stack) (env : env) (line : string) (oc : out_channel) =
  let parts =
    String.split_on_char ' ' (String.trim line)
    |> List.filter (fun s -> s <> "")
  in
  match parts with
  | [] -> ()
  | [ "quit" ] -> raise Quit
  | [ "pop" ] -> (match pop stk with Some _ -> () | None -> push stk Error)
  | [ "add" ] -> add stk env
  | [ "sub" ] -> sub stk env
  | [ "mult" ] -> mult stk env
  | [ "div" ] -> div stk env
  | [ "rem" ] -> rem stk env
  | [ "sign" ] -> sign stk env
  | [ "swap" ] -> swap stk
  | [ "toString" ] -> toString stk
  | [ "println" ] -> println stk oc
  | [ "cat" ] -> cat stk
  | [ "and" ] -> land_cmd stk env
  | [ "or" ] -> lor_cmd stk env
  | [ "not" ] -> lnot_cmd stk env
  | [ "equal" ] -> equal_cmd stk env
  | [ "lessThan" ] -> lt_cmd stk env
  | [ "assign" ] -> assign_cmd stk env
  | [ "if" ] -> if_cmd stk env
  | [ "let" ] -> handle_let stk env
  | [ "end" ] -> handle_end stk env
  | [ "return" ] -> handle_return ()
  | [ "call" ] -> handle_call stk env oc
  | "push" :: _ ->
      let arg = String.sub line 5 (String.length line - 5) |> String.trim in
      let value = parse_constant arg in
      push stk value
  | _ -> push stk Error

(* read all lines from input file*)
let read_and_process_lines ic =
  let rec read_all acc =
    try
      let line = input_line ic in
      read_all (line :: acc)
    with End_of_file -> List.rev acc
  in
  read_all []

(* process lines one by one handles fun definitions/commands *)
let rec process_lines lines stk env oc =
  match lines with
  | [] -> ()
  | line :: rest ->
      let trimmed = String.trim line in
      if trimmed = "" then
        process_lines rest stk env oc
      else
        let parts =
          String.split_on_char ' ' trimmed
          |> List.filter (fun s -> s <> "")
        in
        match parts with
        | [ "fun"; fname; pname ] | [ "inOutFun"; fname; pname ] ->
            let is_inout = (List.hd parts = "inOutFun") in
            let rec collect_body remaining acc =
              match remaining with
              | [] -> [], acc
              | ln :: rest_lines ->
                  let ln_trim = String.trim ln in
                  if ln_trim = "funEnd" then
                    rest_lines, List.rev acc
                  else
                    collect_body rest_lines (ln :: acc)
            in
            let remaining_lines, body = collect_body rest [] in
            let clos =
              {
                func_name = fname;
                param_name = pname;
                body = body;
                env_snapshot = copy_env env;
                is_inout = is_inout;
              }
            in
            env_bind env fname (Closure clos);
            push stk Unit;
            process_lines remaining_lines stk env oc
        | [ "funEnd" ] ->
            process_lines rest stk env oc
        | _ ->
            execute_command stk env line oc;
            process_lines rest stk env oc

(* Main interpreter function *)
let interpreter ((input, output) : string * string) : unit =
  let ic = open_in input in
  let oc = open_out output in
  let stk = empty_stack () in
  let env = empty_env () in
  begin_frames stk;
  (try
     let lines = read_and_process_lines ic in
     process_lines lines (current_frame ()) env oc
   with
   | End_of_file -> ()
   | Quit -> ());
  close_in ic;
  close_out oc
  ;;

  (*files for testing*)
  interpreter ("input.txt", "output.txt")