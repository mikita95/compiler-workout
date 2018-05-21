open GT       
open Language
open List
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
          
let rec reduceArgs f args stack = match args, stack with
                                    | [], t          -> List.rev f, stack
                                    | a::tlA, s::tlS -> reduceArgs ((a, s)::f) tlA tlS

                                               
let check_jmp t h =
  match t with
    | "z"  -> Value.to_int h =  0
    | "nz" -> Value.to_int h <> 0

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | insn :: p' ->
     (match insn with
      | BINOP op -> let y :: x :: stack' = stack in 
                      eval env (cstack, (Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y))) :: stack', c) p'
      | CONST x  -> eval env (cstack, (Value.of_int x) :: stack, c) p'
      | STRING s -> eval env (cstack, (Value.of_string s)::stack, c) p'
      | LD x     -> eval env (cstack, State.eval st x :: stack, c) p'
      | ST x     -> let r :: stack' = stack in 
                      eval env (cstack, stack', (State.update x r st, i, o)) p'
      | STA (x, n) -> let t :: ind, stack' = split (n + 1) stack in 
                        eval env (cstack, stack', (Language.Stmt.update st x t (List.rev ind), i, o)) p'
      | LABEL s  -> eval env conf p'
      | JMP name -> eval env conf (env#labeled name)
      | CJMP (br, name) -> eval env (cstack, tl stack, c) (
                                     if (check_jmp br (hd stack)) 
                                     then (env#labeled name) 
                                     else p')
      | CALL (f, n, p) -> if env#is_label f 
                          then eval env ((p', st)::cstack, stack, c) (env#labeled f) 
                          else eval env (env#builtin conf f n p) p'
      | BEGIN (_, args, locals) -> let redRes, newStack = reduceArgs [] args stack in 
                                     eval env (cstack, newStack, 
                                                 (List.fold_left 
                                                    (fun s (x, v) -> State.update x v s) 
                                                    (State.enter st (args @ locals)) redRes, i, o)) p'
      | END | RET _ -> (match cstack with
                          | (p', st') :: cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) p'
                          | [] -> conf)
      | DROP     -> eval env (cstack, List.tl stack, (st, i, o)) p'
      | DUP      -> eval env (cstack, List.hd stack :: stack, (st, i, o)) p'
      | SWAP     -> let a :: b :: st' = stack in 
                      eval env (cstack, b :: a :: st', (st, i, o)) p'
      | TAG t    -> let a :: st' = stack in 
                      eval env (cstack, (Value.of_int (match a with 
                                                         Value.Sexp (t', _) when t' = t -> 1 
                                                         | _                            -> 0)) 
                                                      :: st', (st, i, o)) p'
      | ENTER l -> let vs, st' = split (List.length l) stack in 
                   let result = List.combine l vs in 
                     eval env (cstack, st', (State.push st (List.fold_left 
                                                              (fun s (x, v) -> State.bind x v s) 
                                                              State.undefined 
                                                              result) l, i, o)) p'
      | LEAVE    -> eval env (cstack, stack, (State.drop st, i, o)) p'
      | SEXP (ex, n) -> let t, stack' = split n stack in 
                          eval env (cstack, (Value.sexp ex (List.rev t)) :: stack', c) p'
     )

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
class env =
    object(self)
        val number = 0
        method next_label = "l" ^ string_of_int number, 
                            {<number = number + 1>}
    end

let getFName name = "L" ^ name

let compCall f args foo pr = let l  = List.map foo (List.rev args) in
                             let ar = List.concat l in
                               ar @ [CALL (getFName f, List.length args, pr)]

let rec compExpr e = match e with
  | Expr.Const n          -> [CONST n]
  | Expr.Var x            -> [LD x]
  | Expr.Binop (op, x, y) -> (compExpr x) @ (compExpr y) @ [BINOP op]
  | Expr.Call (f, args)   -> compCall f args compExpr false
  | Expr.String s         -> [STRING s]
  | Expr.Array a          -> List.flatten (List.map compExpr a) @ 
                             [CALL ("$array", List.length a, false)]
  | Expr.Elem (a, i)      -> compExpr a @ 
                             compExpr i @ 
                             [CALL ("$elem", 2, false)]
  | Expr.Length ex        -> compExpr ex @ 
                             [CALL ("$length", 1, false)]

let rec compPattern e = function
  | Stmt.Pattern.Wildcard    -> [DROP]
  | Stmt.Pattern.Sexp (t, r) -> [DUP; 
                                 TAG t; 
                                 CJMP ("z", e)]                                                 @ 
                                 (List.concat (List.mapi (fun i h -> [DUP; 
                                                                      CONST i; 
                                                                      CALL (".elem", 2, false)] @ 
                                                                      compPattern e h) r))
  | Stmt.Pattern.Ident _     -> [DROP]

let compBind b = let rec compParts = function
  | Stmt.Pattern.Ident _     -> [SWAP]
  | Stmt.Pattern.Sexp (_, r) -> (List.flatten (List.mapi (fun i h -> [DUP; 
                                                                      CONST i; 
                                                                      CALL (".elem", 2, false)] @ 
                                                                     compParts h) r))           @ 
                                                                     [DROP]
  | Stmt.Pattern.Wildcard    -> [DROP]
    in compParts b @ 
       [ENTER (Stmt.Pattern.vars b)]

let rec compile' lbl env = function
  | Stmt.Assign (x, [], e) -> env, compExpr e @ 
                                   [ST x]
  | Stmt.Assign (x, t, e)  -> env, List.flatten (List.map compExpr (t @ [e])) @ 
                                                [STA (x, List.length t)]

  | Stmt.Seq (s1, s2)   -> let newL, ls = env#next_label in
                           let env1, c1 = compile' newL ls   s1 in
                           let env2, c2 = compile' lbl  env1 s2 in 
                           env2, c1           @ 
                                 [LABEL newL] @ 
                                 c2
  | Stmt.Skip           -> env, []
  | Stmt.If (e, s1, s2) ->
      let lelse, env = env#next_label in
      let lfi,   env = env#next_label in
      let env, compiled_then = compile' lbl env s1 in
      let env, compiled_else = compile' lbl env s2 in
        env, (compExpr e          @ 
              [CJMP ("z", lelse)] @ 
              compiled_then       @ 
              [JMP lfi]           @ 
              [LABEL lelse]       @ 
              compiled_else       @ 
              [LABEL lfi])
  | Stmt.While (e, s)  ->
      let lch, env = env#next_label in
      let llp, env = env#next_label in
      let env, compiled_lp = compile' llp env s in
        env, ([JMP lch]   @ 
              [LABEL llp] @ 
              compiled_lp @ 
              [LABEL lch] @ 
              compExpr e  @ 
              [CJMP ("nz", llp)])
  | Stmt.Repeat (s, e) ->
      let llp, env = env#next_label in
      let env, compiled_lp = compile' llp env s in
        env, ([LABEL llp] @ 
              compiled_lp @ 
              compExpr e  @ 
              [CJMP ("z", llp)])
  | Stmt.Call (f, args) -> env, compCall f args compExpr true
  | Stmt.Return result -> env, (match result with None -> [] | Some v -> compExpr v) @ [RET (result <> None)]
  | Stmt.Leave -> env, [LEAVE]
  | Stmt.Case (e, [r, s]) ->
      let pc = compPattern lbl r in
      let env', sc = compile' lbl env (Stmt.Seq (s, Stmt.Leave)) in
        env', compExpr e @ 
              pc         @ 
              compBind r @ 
              sc
  | Stmt.Case (e, brs) ->
      let lbl', _, _, code = 
        List.fold_left 
          (fun (env', nextE, ind, code) (p, s) -> 
             let (res, env), jmp = if   ind  == (List.length brs - 1) 
                                   then (lbl, env'), []
                                   else env#next_label, [JMP lbl] in 
             let pc       = compPattern res p in 
             let env', sc = compile' lbl env (Stmt.Seq (s, Stmt.Leave)) in  
               (env', Some res, ind + 1, ((match nextE with 
                                             None   -> [] 
                                           | Some l -> [LABEL l]) @ 
                                        pc                      @ 
                                        compBind p              @ 
                                        sc                      @
                                        jmp)                   
                                        :: code)) 
        (env, None, 0, []) 
        brs
      in lbl', compExpr e @ 
               (List.flatten (List.rev code))

let compileDefs env (name, (args, locals, body)) = let last, l1 = env#next_label in
                                                   let l2, foo  = compile' last l1 body in
                                                     l2, 
                                                     [LABEL name; 
                                                      BEGIN (name, args, locals)] @ 
                                                     foo                          @ 
                                                     [LABEL last; 
                                                      END]

let collapsDefs l defs = List.fold_left 
                           (fun (l, code) (name, rest) -> 
                              let l1, s = compileDefs l (getFName name, rest) in 
                              l1, s::code) 
                           (l, []) defs

let compile (defs, p) = let last, env    = (new env)#next_label in
                        let l1, c        = compile' last env p in 
                        let l2, code     = collapsDefs l1 defs in
                        (c @ [LABEL last]) @ 
                        [END]              @ 
                        (List.concat code)

