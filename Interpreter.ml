(* parsing util functions *)

let is_lower_case c = 'a' <= c && c <= 'z'

let is_upper_case c = 'A' <= c && c <= 'Z'

let is_alpha c = is_lower_case c || is_upper_case c

let is_digit c = '0' <= c && c <= '9'

let is_alphanum c = is_lower_case c || is_upper_case c || is_digit c

let is_blank c = String.contains " \012\n\r\t" c

let explode s = List.of_seq (String.to_seq s)

let implode ls = String.of_seq (List.to_seq ls)

let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ loop ()
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

(* end of util functions *)

(* parser combinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option = p (explode s)

let pure (x : 'a) : 'a parser = fun ls -> Some (x, ls)

let fail : 'a parser = fun ls -> None

let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> q a ls
  | None -> None

let ( >>= ) = bind

let ( let* ) = bind

let read : char parser =
  fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None

let satisfy (f : char -> bool) : char parser =
  fun ls ->
  match ls with
  | x :: ls ->
    if f x then
      Some (x, ls)
    else
      None
  | _ -> None

let char (c : char) : char parser = satisfy (fun x -> x = c)

let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
  fun ls ->
  match p1 ls with
  | Some (_, ls) -> p2 ls
  | None -> None

let ( >> ) = seq

let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) -> (
      match p2 ls with
      | Some (_, ls) -> Some (x, ls)
      | None -> None)
  | None -> None

let ( << ) = seq'

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) -> Some (x, ls)
  | None -> p2 ls

let ( <|> ) = alt

let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> Some (f a, ls)
  | None -> None

let ( >|= ) = map

let ( >| ) p c = map p (fun _ -> c)

let rec many (p : 'a parser) : 'a list parser =
  fun ls ->
  match p ls with
  | Some (x, ls) -> (
      match many p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1 (p : 'a parser) : 'a list parser =
  fun ls ->
  match p ls with
  | Some (x, ls) -> (
      match many p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> None

let rec many' (p : unit -> 'a parser) : 'a list parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) -> (
      match many' p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1' (p : unit -> 'a parser) : 'a list parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) -> (
      match many' p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> None

let whitespace : unit parser =
  fun ls ->
  match ls with
  | c :: ls ->
    if String.contains " \012\n\r\t" c then
      Some ((), ls)
    else
      None
  | _ -> None

let ws : unit parser = many whitespace >| ()

let ws1 : unit parser = many1 whitespace >| ()

let digit : char parser = satisfy is_digit

let natural : int parser =
  fun ls ->
  match many1 digit ls with
  | Some (xs, ls) -> Some (int_of_string (implode xs), ls)
  | _ -> None

let literal (s : string) : unit parser =
  fun ls ->
  let cs = explode s in
  let rec loop cs ls =
    match (cs, ls) with
    | [], _ -> Some ((), ls)
    | c :: cs, x :: xs ->
      if x = c then
        loop cs xs
      else
        None
    | _ -> None
  in
  loop cs ls

let keyword (s : string) : unit parser = literal s >> ws >| ()

(* end of parser combinators *)

type const =
  | Name of string
  | Int of int
  | Unit
  | Bool of string

type com =
  | Push of const
  | Pop of int
  | Trace of int
  | Add of int
  | Sub of int
  | Mul of int
  | Div of int
  | And
  | Or
  | Not
  | Equal
  | Lte
  | Local
  | Global
  | Lookup
  | BeginEnd of coms
  | IfElse of coms * coms
  | Fun of value * value * coms
  | Call
  | TryEnd of coms
  | Switch of (value * coms) list

and coms = com list

and value = 
  | I of int
  | B of string
  | U
  | N of string
  | Clo of ((value*value) list)*value*value*coms

let intparser =
  fun ls ->
  match ls with
  | '-'::t -> (match (natural t) with
      | Some (x, ls) -> Some (-x, ls)
      | None -> None)
  | _ -> (match (natural ls) with
      | Some (x, ls) -> Some (x, ls)
      | None -> None)

let int_parser =
  let* a = intparser in pure (Int a) << ws

let is_sign x = x = '_' || x = '\''

let commands = ["Push"; "Pop"; "Trace"; "Add"; "Sub"; "Mul"; "Div"; "And"; "Or"; "Not"; "Equal"; "Lte"; "Local"; "Global"; "Lookup"; "Begin"; "End"; "If"; "Else"; "Fun"; "Call"; "Try"; "Switch"; "Case"]

let rec exists x ls = 
  match ls with
  | [] -> false
  | h::t -> if h = x then true else exists x t

let name_parser =
  let* c = satisfy is_alpha in
  let* cs = many (satisfy (fun x -> is_digit x || is_alpha x || is_sign x)) in
  let s = implode (c :: cs) in
  if exists s commands then fail else pure (Name s) << ws

let boolparser =
  fun ls ->
  match ls with
  | 'T'::'r'::'u'::'e'::t -> Some ("True", t)
  | 'F'::'a'::'l'::'s'::'e'::t -> Some ("False", t)
  | _ -> None

let bool_parser =
  let* a = boolparser in pure (Bool a) << ws

let unit_parser = 
  let* _ = keyword "()" in pure (Unit) << ws

let const_parser () = int_parser <|> unit_parser <|> bool_parser <|> name_parser

let rec push_parser () =
  let* _ = keyword "Push" in
  let* a = const_parser () in pure (Push a)

and pop_parser () =
  let* _ = keyword "Pop" in
  let* a = int_parser in 
  match a with
  | Int x -> pure (Pop x)
  | _ -> fail

and trace_parser () =
  let* _ = keyword "Trace" in
  let* a = int_parser in
  match a with
  | Int x -> pure (Trace x)
  | _ -> fail

and add_parser () =
  let* _ = keyword "Add" in
  let* a = int_parser in
  match a with
  | Int x -> pure (Add x)
  | _ -> fail

and div_parser () =
  let* _ = keyword "Div" in
  let* a = int_parser in
  match a with
  | Int x -> pure (Div x)
  | _ -> fail

and sub_parser () =
  let* _ = keyword "Sub" in
  let* a = int_parser in
  match a with
  | Int x -> pure (Sub x)
  | _ -> fail

and mul_parser () =
  let* _ = keyword "Mul" in
  let* a = int_parser in
  match a with
  | Int x -> pure (Mul x)
  | _ -> fail

and and_parser () =
  let* _ = keyword "And" in pure (And)

and or_parser () =
  let* _ = keyword "Or" in pure (Or)

and not_parser () =
  let* _ = keyword "Not" in pure (Not)

and equal_parser () =
  let* _ = keyword "Equal" in pure (Equal)

and lte_parser () = 
  let* _ = keyword "Lte" in pure (Lte)

and local_parser () =
  let* _ = keyword "Local" in pure (Local)

and global_parser () =
  let* _ = keyword "Global" in pure (Global)

and lookup_parser () =
  let* _ = keyword "Lookup" in pure (Lookup)

and beginend_parser () =
  let* _ = keyword "Begin" in
  let* a = coms_parser () in
  let* _ = keyword "End" in pure (BeginEnd a)

and ifelse_parser () =
  let* _ = keyword "If" in
  let* a = coms_parser () in
  let* _ = keyword "Else" in
  let* b = coms_parser () in
  let* _ = keyword "End" in pure (IfElse (a, b))

and fun_parser () =
  let* _ = keyword "Fun" in
  let* a = name_parser in
  let* b = name_parser in
  let* c = coms_parser () in
  let* _ = keyword "End" in 
  match (a, b) with
  | (Name x, Name y) -> pure (Fun (N x, N y, c))
  | _ -> fail

and call_parser () =
  let* _ = keyword "Call" in pure (Call)

and tryend_parser () =
  let* _ = keyword "Try" in
  let* a = coms_parser () in
  let* _ = keyword "End" in pure (TryEnd a)

and case_parser () =
  let* _ = keyword "Case" in
  let* a = int_parser in
  let* b = (coms_parser ()) << ws in 
  match a with
  | Int x -> pure (I x, b)
  | _ -> fail

and switch_parser () =
  let* _ = keyword "Switch" in
  let* a = many(case_parser ()) in
  let* _ = keyword "End" in pure (Switch a)


and com_parser () = push_parser () <|> pop_parser () <|> trace_parser () <|> add_parser () <|> div_parser () <|> sub_parser () <|> mul_parser () <|> and_parser () <|> or_parser () <|> not_parser () <|> equal_parser () <|> lte_parser () <|> local_parser () <|> global_parser () <|> lookup_parser () <|> beginend_parser () <|> ifelse_parser () <|> fun_parser () <|> call_parser () <|> tryend_parser () <|> switch_parser ()

and coms_parser () = many (com_parser ())


let pop ls n =
  if n<0 then None
  else
    let rec aux acc ls n = 
      match n with
      | 0 -> Some (acc, ls)
      | x -> match ls with
        | [] -> None
        | h::t -> aux (h::acc) t (n-1) in
    match (aux [] ls n) with
    | Some (a, b) -> Some b
    | None -> None

let trace ls n =
  if n<0 then None
  else
    let rec aux acc ls n = 
      match n with
      | 0 -> Some (acc, ls)
      | x -> match ls with
        | [] -> None
        | h::t -> (match h with
            | I i -> aux ((string_of_int i)::acc) t (n-1)
            | N na -> aux (na::acc) t (n-1)
            | B b -> aux (b::acc) t (n-1)
            | U -> aux ("()"::acc) t (n-1)
            | _ -> None) in
    aux [] ls n

let rec is_int str = 
  match (explode str) with
  | '-'::t -> is_int (implode t)
  | [] -> true
  | h::t -> if (is_digit h) then is_int (implode t) else false

let rec is_all_int ls = 
  match ls with
  | [] -> true
  | h::t -> if (is_int h) = false then false else is_all_int t

let add ls n =
  let lss = trace ls n in
  match lss with
  | None -> None
  | Some (a, b) ->
    if (is_all_int a) = false then None else
      (let sc = (List.map int_of_string a) in
       Some ((List.fold_left (+) 0 sc), b))

let sub ls n =
  let lss = trace ls n in
  match lss with
  | None -> None
  | Some (a, b) ->
    if (is_all_int a) = false then None else
      let sc = List.rev (List.map int_of_string a) in
      match sc with
      | [] -> Some (0, b)
      | h::t -> Some ((h - (List.fold_left (+) 0 t)), b)

let mul ls n =
  let lss = trace ls n in
  match lss with
  | None -> None
  | Some (a, b) ->
    if (is_all_int a) = false then None else
      let sc = (List.map int_of_string a) in
      Some ((List.fold_left (fun x y -> x * y) 1 sc), b)

let div ls n =
  let lss = trace ls n in
  match lss with
  | None -> None
  | Some (a, b) ->
    if (is_all_int a) = false then None else
      let sc = List.rev (List.map int_of_string a) in
      match sc with
      | [] -> Some (1, b)
      | h::t -> match (List.fold_left (fun x y -> x * y) 1 t) with
        | 0 -> None
        | x -> Some ((h / x), b)

let boland ls = 
  let lss = trace ls 2 in
  (match lss with
   | None -> None
   | Some (log, rest) -> (match log with
       | "True"::"False"::[] -> Some (B "False"::rest)
       | "False"::"True"::[] -> Some (B "False"::rest)
       | "False"::"False"::[] -> Some (B "False"::rest)
       | "True"::"True"::[] -> Some (B "True"::rest)
       | _ -> None))

let bolor ls = 
  let lss = trace ls 2 in
  (match lss with
   | None -> None
   | Some (log, rest) -> (match log with
       | "True"::"False"::[] -> Some (B "True"::rest)
       | "False"::"True"::[] -> Some (B "True"::rest)
       | "False"::"False"::[] -> Some (B "False"::rest)
       | "True"::"True"::[] -> Some (B "True"::rest)
       | _ -> None))

let bolnot ls = 
  let lss = trace ls 1 in
  (match lss with
   | None -> None
   | Some (log, rest) -> (match log with
       | "True"::[] -> Some (B "False"::rest)
       | "False"::[] -> Some (B "True"::rest)
       | _ -> None))

let is_bol s =
  s = "True" || s = "False"

let is_name s = match s with N _ -> true | _ -> false

let is_value s = match s with
  | I _ -> true
  | N _ -> true
  | U -> true
  | Clo _ -> true
  | B _ -> true
  | _ -> false

let is_both_int ls = 
  is_int (List.hd ls) && is_int (List.hd (List.tl ls))

let equal ls = 
  let lss = trace ls 2 in
  (match lss with
   | None -> None
   | Some (log, rest) -> (if is_both_int log then
                            (if (int_of_string (List.hd log)) = (int_of_string (List.hd (List.tl log))) then Some (B "True"::rest)
                             else Some (B "False"::rest))
                          else None))

let lte ls =
  let lss = trace ls 2 in
  (match lss with
   | None -> None
   | Some (log, rest) -> (if is_both_int log then
                            (if (int_of_string (List.hd log)) >= (int_of_string (List.hd (List.tl log))) then Some (B "True"::rest)
                             else Some (B "False"::rest))
                          else None))

let rec update env name value =
  match env with
  | [] -> (name, value)::env
  | h::t -> (match h with
      | (n, v) -> if n = name then (n, value)::t
        else (n, v)::(update t name value))

let local stack lo =
  match stack with
  | h1::h2::t -> if (is_name h1) = false then None 
    else Some ((update lo h1 h2), t) 
  | _ -> None

let rec find_key ls key =
  match ls with
  | [] -> None
  | h::t -> (match h with
      | (a, b) -> (if a = key then (Some b) else find_key t key))

let lookup stack gl lo =
  (match stack with
   | h::t -> if (is_name h) = false then None
     else (match (find_key lo h) with
         | Some a -> Some (a::t)
         | None -> (match (find_key gl h) with
             | Some a -> Some (a::t)
             | None -> None))
   | _ -> None)


(*let lookup stack gl lo =
  let lss = trace stack 1 in
  match lss with
  | None -> None
  | Some (log, rest) -> (match log with
      | h::_ -> (if (is_name h) then 
                   (match (find_key lo h) with 
                    | None -> (match (find_key gl h) with
                        | None -> None
                        | Some a -> Some (a::rest))
                    | Some a -> Some (a::rest))
                 else None)
      | [] -> None)*)
(* TODO *)
let interp (src : string) : string list = 
  let co = parse (ws >> coms_parser ()) src in
  match co with
  | Some (comls, []) ->
    (let rec inter glo loc sta log cmd = 
       match cmd with
       | [] -> (glo, loc, sta, log, [])
       | (Push (Int i))::t -> inter glo loc ((I i)::sta) log t
       | (Push (Name n))::t -> inter glo loc ((N n)::sta) log t
       | (Push (Unit))::t -> inter glo loc (U::sta) log t
       | (Push (Bool b))::t -> inter glo loc ((B b)::sta) log t
       | (Pop i)::t -> (match (pop sta i) with
           | Some a -> inter glo loc a log t
           | None -> (glo, loc, sta, ["Error"], t))
       | (Trace i)::t -> (match (trace sta i) with
           | Some (r, rest) -> inter glo loc rest (r@log) t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Add i)::t -> (match (add sta i) with
           | Some (r, rest) -> inter glo loc ((I r)::rest) log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Sub i)::t -> (match (sub sta i) with
           | Some (r, rest) -> inter glo loc ((I r)::rest) log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Mul i)::t -> (match (mul sta i) with
           | Some (r, rest) -> inter glo loc ((I r)::rest) log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Div i)::t -> (match (div sta i) with
           | Some (r, rest) -> inter glo loc ((I r)::rest) log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (And)::t -> (match (boland sta) with
           | Some r -> inter glo loc r log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Or)::t -> (match (bolor sta) with
           | Some r -> inter glo loc r log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Not)::t -> (match (bolnot sta) with
           | Some r -> inter glo loc r log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Equal)::t -> (match (equal sta) with
           | Some r -> inter glo loc r log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Lte)::t -> (match (lte sta) with
           | Some r -> inter glo loc r log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Local)::t -> (match (local sta loc) with
           | Some (r, rest) -> inter glo r (U::rest) log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Global)::t -> (match (local sta glo) with
           | Some (r, rest) -> inter r loc (U::rest) log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (Lookup)::t -> (match (lookup sta glo loc) with
           | Some r -> inter glo loc r log t
           | None -> (glo, loc, sta, ["Error"], []))
       | (BeginEnd comm)::t -> (match (inter glo loc [] log comm) with
           | (_, _, _, ["Error"], _) -> (glo, loc, sta, ["Error"], [])
           | (g, l, s, lg, c) -> (match s with
               | h::_ -> inter g loc (h::sta) lg t
               | [] -> (glo, loc, sta, ["Error"], [])))
       | (IfElse (comm1, comm2))::t -> (match sta with
           | [] -> (glo, loc, sta, ["Error"], [])
           | h::tl -> (match h with
               | B "True" -> (match (inter glo loc tl log comm1) with
                   | (_, _, _, ["Error"], _) -> (glo, loc, sta, ["Error"], [])
                   | (g, l, s, lg, c) -> inter g l s lg t)
               | B "False" -> (match (inter glo loc tl log comm2) with
                   | (_, _, _, ["Error"], _) -> (glo, loc, sta, ["Error"], [])
                   | (g, l, s, lg, c) -> inter g l s lg t)
               | _ -> (glo, loc, sta, ["Error"], [])))
       | (Fun (fname, arg, comm))::t -> let l = loc in inter glo (update loc fname (Clo (l, fname, arg, comm))) sta log t
       | (Call)::t -> (match sta with
           | h1::h2::tl -> (match h1 with
               | Clo (l, f, a, c) -> (match (inter glo (update (update l a h2) f h1) [] log c) with
                   | (_, _, _, ["Error"], _) -> (glo, loc, sta, ["Error"], [])
                   | (g, l, s, lg, cm) -> (match s with
                       | [] -> (glo, loc, sta, ["Error"], [])
                       | h::_ -> inter g loc (h::tl) lg t))
               | _ -> (glo, loc, sta, ["Error"], []))
           | _ -> (glo, loc, sta, ["Error"], []))
       | (TryEnd comm)::t -> (match (inter glo loc [] log comm) with
           | (g, _, _, ["Error"], _) -> inter g loc sta log t
           | (gl, _, st, lg, _) -> (match st with
               | [] -> (glo, loc, sta, ["Error"], [])
               | h::_ -> inter gl loc (h::sta) lg t))
       | (Switch cases)::t -> (match sta with
           | I a::tl -> (match (find_key cases (I a)) with
               | None -> (glo, loc, sta, ["Error"], [])
               | Some x -> (match (inter glo loc tl log x) with
                   | (_, _, _, ["Error"], _) -> (glo, loc, sta, ["Error"], [])
                   | (g, l, s, lg, c) -> inter g l s lg t))
           | _ -> (glo, loc, sta, ["Error"], []))



       | _ -> (glo, loc, sta, ["Error"], [])



     in match inter [] [] [] [] comls with
     | (a, b, c, d, e) -> d)
  | _ -> ["Error"]

(* Calling (main "test.txt") will read the file test.txt and run interp on it.
   This is only used for debugging and will not be used by the gradescope autograder. *)
let main fname =
  let src = readlines fname in
  interp src
