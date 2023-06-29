load "Random";
load "Listsort";
load "Int";
load "Bool";

val rand = Random.newgen();

datatype operation = ADD | GEQ | EQ

datatype type_L = int  
  | unit  
  | bool 
  | proc 
  | functype of type_L * type_L;

type loc = string
datatype type_loc = intref;

type store = (loc * int) list
type typeE = (loc * type_loc) list 

datatype exp = Boolean of bool
  | Integer of int
  | Op of exp * operation * exp
  | If of exp * exp * exp
  | Assign of loc * exp
  | Skip
  | Seq of exp * exp
  | While of exp * exp
  | Var of int
  | Deref of loc
  | Fn of type_L * exp
  | App of exp * exp
  | App_CBN of exp * exp
  | Let of type_L * exp * exp
  | Fix of exp
  | Fix_CBN of exp
  | Parallel of exp * exp
  | Await of exp * exp
  | RepPar of exp
  | AwtPar of exp

fun isValue (Integer n) = true
  | isValue (Boolean b) = true
  | isValue (Fn (t,e)) = true (* first-class citizen *)
  | isValue (Skip) = true
  | isValue _ = false


fun replace e n (Integer n') = Integer n'
  | replace e n (Boolean b) = Boolean b
  | replace e n (Op (e1,opr,e2)) = Op (replace e n e1,opr,replace e n e2)
  | replace e n (If (e1,e2,e3)) = If (replace e n e1, replace e n e2, replace e n e3)
  | replace e n (Assign (l,e1)) = Assign(l,replace e n e1)
  | replace e n (Deref l) = Deref l
  | replace e n (Skip) = Skip
  | replace e n (Seq (e1,e2)) = Seq (replace e n e1,replace e n e2)
  | replace e n (While (e1,e2)) = While (replace e n e1,replace e n e2)
  | replace e n (Fn (t,e1)) = Fn (t,replace e (n + 1) e1)
  | replace e n (App (e1,e2)) = App (replace e n e1,replace e n e2)
  | replace e n (App_CBN (e1,e2)) = App_CBN (replace e n e1,replace e n e2)
  | replace e n (Let (t,e1,e2)) = Let (t,replace e n e1,replace e (n + 1) e2)
  | replace e n (Var n') = if n = n' then e else Var n'
  | replace e n (Fix e1) = Fix (replace e n e1)
  | replace e n (Fix_CBN e1) = Fix_CBN (replace e n e1)
  | replace e n (Parallel (e1,e2)) = Parallel (replace e n e1,replace e n e2)
  | replace e n (Await (e1,e2)) = Await (replace e n e1,replace e n e2)
  | replace e n (RepPar e1) = RepPar (replace e n e1)
  | replace e n (AwtPar e1) = AwtPar (replace e n e1)





(* is in the store or null
  the store has type (loc * int ) list  *)
fun loc_controller ( [], l ) = NONE
  | loc_controller ( (location, value)::pairs, l) = 
    if (location = l) then SOME (value)
    else loc_controller (pairs, l)


(* fn:store * (loc*int)->store option *)

(* fn: (''a * 'b) list -> (''a * 'b) list -> ''a * 'b -> (''a * 'b) list option *)

(*
  Front is a list that starts as empty then is filled with the pairs when i go through the list
  If i find the location thta i ned to modify  i return the new list(Front) with the rest of the store where
  i have modified the value of the location
*)
fun update'  front [] (l,n) = NONE
  |  update'  front ((l',n')::pairs) (l,n) = 
    if l=l' then 
      SOME(front @ ((l,n)::pairs) )
    else 
      update' ((l',n')::front) pairs (l,n)

fun update (s, (l,n)) = update' [] s (l,n)

fun select [] m = NONE
  | select (hd::tl) m = if m=0 then SOME hd else select tl (m-1)

fun infertype gamma (Integer n) = SOME int
  | infertype gamma (Boolean b) = SOME bool
  | infertype gamma (Op (e1,oper,e2)) 
    = (case (infertype gamma e1, oper, infertype gamma e2) of
        (SOME int, ADD, SOME int) => SOME int
        |(SOME int, GEQ, SOME int) => SOME bool
        |(SOME int, EQ, SOME int) => SOME bool (* To implemenent the Fibonnaci *)
        |_ => NONE)
  | infertype gamma (If (e1,e2,e3)) 
    = (case (infertype gamma e1, infertype gamma e2, infertype gamma e3) of
        (SOME bool, SOME type_e2, SOME type_e3) => 
        (if type_e2=type_e3 then SOME type_e2 else NONE)
        |_ => NONE)
  | infertype gamma (Deref l) 
    = (case loc_controller ((#1 gamma),l) of
        SOME intref => SOME int
        | NONE => NONE)
  | infertype gamma (Assign (l,e)) 
    = (case (loc_controller ((#1 gamma),l), infertype gamma e) of
      (SOME intref,SOME int) => SOME unit
      | _ => NONE)
  | infertype gamma (Skip) = SOME unit
  | infertype gamma (Var n) = select (#2 gamma) n
  | infertype gamma (Seq (e1,e2))  
    = (case (infertype gamma e1, infertype gamma e2) of
      (SOME unit, SOME type_e2) => SOME type_e2
      | _ => NONE )
  | infertype gamma (While (e1,e2)) 
    = (case (infertype gamma e1, infertype gamma e2) of
        (SOME bool, SOME unit) => SOME unit 
        | _ => NONE )
  | infertype gamma (Fn (t,e)) 
    = (case (infertype (#1 gamma, t::(#2 gamma)) e) of 
      (SOME type_e1 ) => SOME (functype (t,type_e1))
      | _ => NONE) (* Diff *)
  | infertype gamma (App (function,arg))
    = (case (infertype gamma function, infertype gamma arg) of
        (SOME (functype (func_in, func_out)), SOME type_arg) => 
        (if func_in = type_arg then SOME func_out else NONE)
        | _ => NONE)
  | infertype gamma (App_CBN (function,arg))
    = (case (infertype gamma function, infertype gamma arg) of
        (SOME (functype (t1, t2)), SOME type_arg) => 
        (if t1 = type_arg then SOME t2 else NONE)
        | _ => NONE)
  | infertype gamma (Let (t,e1,e2)) 
    = (case (infertype gamma e1, infertype (#1 gamma, t::(#2 gamma)) e2) of
        (SOME type_e1, SOME type_e2) => if type_e1 = t then SOME type_e2 else NONE
        | _ => NONE)
  | infertype gamma (Fix e) 
    = (case (infertype gamma e) of
        SOME (functype(functype (func_in, func_out), (functype(func_in', func_out')))) =>
        (if func_in = func_in' andalso func_out = func_out' 
          then SOME (functype (func_in, func_out)) else NONE)
        | _ => NONE)
  | infertype gamma (Fix_CBN e) 
    = (case (infertype gamma e) of
        SOME (functype(functype (func_in, func_out), (functype(func_in', func_out')))) =>
        (if func_in = func_in' andalso func_out = func_out' 
          then SOME (functype (func_in, func_out)) else NONE)
        | _ => NONE)
  | infertype gamma (Parallel (e1, e2))
    = (case (infertype gamma e1, infertype gamma e2) of
        (SOME unit, SOME unit) => SOME proc
        |(SOME proc, SOME proc) => SOME proc
        | _ => NONE)
  | infertype gamma (Await (e1,e2))
    = ( case (infertype gamma e1, infertype gamma e2) of
        (SOME bool, SOME unit) => SOME unit
        | _ => NONE)
  | infertype gamma (RepPar (e))
    = (case infertype gamma e of
        SOME unit => SOME proc
        | _ => NONE)
  | infertype gamma (AwtPar (e))
    = (case infertype gamma e of
        SOME unit => SOME proc
        | _ => NONE);


(* small-step *)
fun reduce (Integer n,s) = NONE
    |reduce (Boolean b,s) = NONE
    |reduce (Op (e1,oper,e2),s) = 
      (case (e1,oper,e2) of
        (* op + *)
        (Integer x1, ADD, Integer x2) => SOME(Integer (x1+x2), s)
        (* op >= *)
        |(Integer x1, GEQ, Integer x2) => SOME(Boolean (x1 >= x2), s)
        (* op = *)
        |(Integer x1, EQ, Integer x2) => SOME(Boolean (x1 = x2), s)
        (* otherwise is op1 or op2 *)
        |(e1,oper,e2) => (
          (* op-2 *)                                               
          if (isValue e1) then(                                        
            case reduce (e2,s) of 
              SOME (e2',s') => SOME (Op(e1,oper,e2'),s')
              | NONE => NONE )                           
          (* op-1 *)
          else (                                                 
            case reduce (e1,s) of 
                SOME (e1',s') => SOME(Op(e1',oper,e2),s')
                |NONE => NONE ) 
        )
      )
    |reduce (If (e1,e2,e3),s) =
      (case e1 of
        Boolean(true) => SOME(e2,s)                           
        |Boolean(false) => SOME(e3,s) 
        (* e1 is a expression*)                         
        | _ => (case reduce (e1,s) of
                  SOME(e1',s') => SOME(If(e1',e2,e3),s')
                  | NONE => NONE )
      )
    |reduce (Deref l,s) = 
        (case loc_controller(s,l) of                
          SOME n => SOME(Integer n,s)                          
          | NONE => NONE
        )                
    |reduce (Assign (l,e),s) =       
      (case e of                                                 
          Integer n => (case update (s,(l,n)) of 
                          SOME s' => SOME(Skip, s')           
                          | NONE => NONE)                                   
          | _ => (case reduce (e,s) of                           
                    SOME (e',s') => SOME(Assign (l,e'), s')    
                    | NONE => NONE  )
      )                          
    | reduce (While (e1,e2),s) = SOME( If(e1,Seq(e2,While(e1,e2)),Skip),s)
    | reduce (Skip,s) = NONE
    | reduce (Seq (e1,e2),s) =                                   
      (case e1 of                                                 
        Skip => SOME(e2,s)                                     
        | _ => (case reduce (e1,s) of                           
                  SOME (e1',s') => SOME(Seq (e1',e2), s')       
                  | NONE => NONE )
      )
    | reduce (Fn (arg_type, exp), s) = NONE
    | reduce (App (fnc,arg),s) =
      (case fnc of
        Fn (arg_type, exp) => (
          if (isValue arg) then SOME(replace arg 0 exp, s)
          else (case reduce (arg,s) of (* APP-2 *)
                  SOME (arg',s') => SOME(App (fnc,arg'), s')
                  | NONE => NONE)
        )
        | _ => (case reduce (fnc,s) of (* APP-1 *)
                  SOME (fnc',s') => SOME (App (fnc',arg), s')
                  | NONE => NONE)
      )
    | reduce (App_CBN (fnc,arg),s) =
      (case fnc of
        Fn (arg_type, exp) => ( SOME(replace arg 0 exp, s)
        )
        | _ => (case reduce (fnc,s) of (* APP-CBN *)
                  SOME (fnc',s') => SOME (App_CBN (fnc',arg), s')
                  | NONE => NONE)
      )
    | reduce (Fix_CBN (e),s) = SOME(App_CBN (e, Fix_CBN (e)),s)
    | reduce (Fix (e), s) =
      (case e of
        Fn (functype(arg_type, exp),exp2) => SOME(App(e, Fn(arg_type, App(Fix(e), Var 0))), s) (* CBV-FIX *)
        | _ => (case reduce (e,s) of
                  SOME (e',s') => SOME (Fix (e'), s')
                  | NONE => NONE)
      )
    | reduce (Let (x,e1,e2),s) = 
      (if (isValue e1) then SOME(replace e1 0 e2, s)
      else (case reduce (e1,s) of
              SOME (e1',s') => SOME(Let (x,e1',e2), s')
              | NONE => NONE)
      )
    | reduce (Parallel (e1,e2),s) = ( 
      (*
        I need to choose between e1 and e2 (Choice-L or Choice-R) and to simulate the random choice I use the function rand
        rand returns a random number between 0 and 1, if the number is less than 0.5 I choose e1, otherwise e2
        Assume that I have chosen e1 (e1 is the expression that will be executed)
            - Check if e1 is a skip, if it is then I return e2 according to the rule
            - Check if e1 can execute a step:
              - If e1 can execute a step then I return the parallel computation with e1'
              - If e1 cannot execute a step then I check if e2 can execute a step:
                - Check if e2 is a Skip, if yes then i simply return e1
                - Check if e2 can execute a step:
                  - If e2 can execute a step then I return the parallel computation with e2'
                  - If e2 cannot execute a step then I return NONE since there is nothing to do
        Same reasoning for e2 aswell if I had chosen e2
      *)
      (* take random choice between e1 and e2*)
      if Random.random rand>=0.5 then (
        (* execute e1 *)
        case (e1,e2,s) of
          (* e1 is a skip*)
          (Skip,e2,s) => SOME(e2,s)
          (* e1 can be a expression or a not executable*)                         
          |(e1,e2,s) => (
            case reduce (e1,s) of
              SOME(e1',s') => SOME(Parallel(e1',e2),s')
              | NONE => (
                (* check if can execute e2*)
                case (e1,e2,s) of
                  (e1,Skip,s) => SOME(e1,s)
                  |(e1,e2,s) => (
                    case reduce (e2, s) of
                      SOME(e2',s') => SOME(Parallel(e1,e2'),s')
                      | NONE => NONE (*No steps*)
                  )
                )
            )
      )else(
        (* execute e2 *)
        case (e1,e2,s) of
          (* e2 is a skip*)
          (e1,Skip,s) => SOME(e1,s)
          (* e2 can be a expression or a not executable*)                         
          |(e1,e2,s) => (
            case reduce (e2,s) of
              SOME(e2',s') => SOME(Parallel(e1,e2'),s')
              |NONE => (
                (* check if can execute e1*)
                case (e1,e2,s) of
                  (Skip,e2,s) => SOME(e2,s)
                  |(e1,e2,s) => (
                    case reduce (e1,s) of
                      SOME(e1',s') => SOME(Parallel(e1',e2),s')
                      | NONE => NONE (*No steps*)
                    )
                  )
              )
      )
    )
    | reduce ( Await (e1,e2),s) = (
      (*
        For the Await I had to define the function bigStep to be able to evaluate completely the guard and then to execute
        in a single step the body of the Await in case the guard is true (I couldn't use evaluate because it uses reduce
        which has not been defined at this point).
        To execute the Await i follow these steps:
          - Check the guard e1 (bigStep(e1,s)) if it is true (Boolean(true)) then I can execute completely e2 (bigStep(e2,s'))
            - If e2 has more steps to execute it will arrive to a Skip
            - If e2 doesn't have steps to execute then I return NONE

      *)
        (* need to use reduce in one step so define a bigstep function*)
      let fun bigStep(e, s) = 
        (case reduce(e,s) of
            SOME(e',s') => bigStep(e',s')
            | NONE => (e,s)
        ) 
      in
        case bigStep(e1,s) of
          (Boolean(true), s') => (
            case bigStep(e2,s') of
              (Skip, s'') => SOME(Skip, s'')
              | _ => NONE
          )
          |_ => NONE
      end
    )
    | reduce (RepPar (e), s) =
      (let val P = Fn(functype(unit,unit), Fn(unit, Parallel(Var 0, App_CBN(Var 1, Var 0))))
          in SOME(App_CBN(Fix_CBN(P), e), s)
       end
      )
    | reduce (AwtPar (e),s) =
      (let val P = Fn(functype(unit,unit), Fn(unit, Parallel(Await(Boolean(true), Var 0), App_CBN(Var 1, Var 0))))
          in SOME(App_CBN(Fix_CBN(P), e), s)
       end
      );



fun printop ADD = "+"
  | printop GEQ = ">="
  | printop EQ  = "=="

fun printexp (Integer n) = Int.toString n
  | printexp (Boolean b) = Bool.toString b
  | printexp (Op (e1,oper,e2)) 
    = "(" ^ (printexp e1) ^ (printop oper) ^ (printexp e2) ^ ")"
  | printexp (If (e1,e2,e3)) 
    = "If " ^ (printexp e1 ) ^ " then " ^ (printexp e2) ^ " else " ^ (printexp e3)
  | printexp (Deref l) = "!" ^ l
  | printexp (Assign (l,e)) =  l ^ ":=" ^ (printexp e )
  | printexp (Skip) = "Skip"
  | printexp (Seq (e1,e2)) =  (printexp e1 ) ^ ";" ^ (printexp e2)
  | printexp (While (e1,e2)) =  "While " ^ (printexp e1 ) ^ " do " ^ (printexp e2)
  | printexp (Fn (t,e)) = "Fn " ^ (printexp e)
  | printexp (App (e1,e2)) = "App(" ^(printexp e1 ) ^ ", " ^ (printexp e2) ^ ")"
  | printexp (App_CBN (e1,e2)) = "_App(" ^(printexp e1 ) ^ ", " ^ (printexp e2) ^ ")"
  | printexp (Var x) = "Var(" ^ (Int.toString x) ^ ")"
  | printexp (Fix (e)) = "Fix(" ^ (printexp e) ^ ")"
  | printexp (Fix_CBN (e)) = "_Fix(" ^ (printexp e) ^ ")"
  | printexp (Parallel (e1, e2)) =  "("^(printexp e1 ) ^ " || " ^ (printexp e2)^")"
  | printexp (Await (e1,e2)) = "Await "^ (printexp e1) ^ " protect " ^ (printexp e2) ^ " end"
  | printexp (RepPar(e)) = "RepPar(" ^ (printexp e) ^")"
  | printexp (AwtPar(e)) = "AwtPar(" ^ (printexp e) ^")"

fun printstore' [] = ""
  | printstore' ((l,n)::pairs) = l ^ "=" ^ (Int.toString n) ^ " " ^ (printstore' pairs)

fun printstore pairs = 
    let val pairs' = Listsort.sort 
      (fn ((l,n),(l',n')) => String.compare (l,l'))
      pairs
    in
        "{" ^ printstore' pairs' ^ "}" end

fun printconf (e,s) = "<" ^ (printexp e) ^ ", " ^ (printstore s) ^ ">"

fun printreduce' (e,s) = 
    case reduce (e,s) of 
      SOME (e',s') => 
        ( TextIO.print ("\n -->  " ^ printconf (e',s') ^ "\n"); printreduce' (e',s'))
      |NONE => (TextIO.print "\n -/->  " ; 
                if isValue e then 
                  TextIO.print "(a value)\n" 
                else 
                  TextIO.print "(stuck - not a value)" )

fun printreduce (e,s) = (TextIO.print ("\n " ^ (printconf (e,s))); printreduce' (e,s));

fun evaluate (e,s) =(case reduce (e,s) of 
                      NONE => (e,s)
                      |SOME (e',s') => evaluate (e',s')
                    );



(*---------------------------- Examples -----------------------------------*)
(*----------To test them remove the comments and try one by one *-°------- *)

(*
TextIO.print("\n ------Create fibonacci function using APP/FIX/FN ------------------\n");

printreduce(
  Assign("y",App(Fix(Fn(functype(int, int), Fn(int, If(Op(Var 0, EQ, Integer 0), Integer 0, If(Op(Var 0, EQ, Integer 1), Integer 1, Op(App(Var 1, Op(Var 0, ADD, Integer ~1)), ADD, App(Var 1, Op(Var 0, ADD, Integer ~2)))))))), Integer 15)),
  [("y",0)] (*Should print <Skip, {y=610 }>  meaning we saved the 15nth number in the fibonacci sequence in y*)
  );
*)


(*CBN Fibonacci  Since i had to define the CBN anyways  *)
(*
TextIO.print("\n ------Create fibonacci function using App_CBN/FIX_CBN/FN ------------------\n");

printreduce(
  Assign("y",App_CBN(Fix_CBN(Fn(functype(int, int), Fn(int, If(Op(Var 0, EQ, Integer 0), Integer 0, If(Op(Var 0, EQ, Integer 1), Integer 1, Op(App_CBN(Var 1, Op(Var 0, ADD, Integer ~1)), ADD, App_CBN(Var 1, Op(Var 0, ADD, Integer ~2)))))))), Integer 10)),
  [("y",0)] (*Should print <Skip, {y=55 }>  meaning we saved the 10nth number in the fibonacci sequence in y*)
  );

*)

(*
TextIO.print("\n ====== Checkin if the parallel operator works ======\n");

printreduce(
  Assign("y",RepPar(Seq(Assign("y", Integer 0 ),Assign("y", Op(Deref "y", ADD, Integer 1))))),
  [("y",0)] (* In this case because of interleaving y can take values from 0,1 and in some cases 2,3,4... when 
            we do some 'assign 0' first and then the remaining incrments *)
  );
*)


(*
TextIO.print("\n ====== Checkin if the AwtPar operator works ======\n");

printreduce(
  Assign("y",AwtPar( Assign("y", Op(Deref "y", ADD, Integer 1)))),
  [("y",0)] (* As stated in slide 37/38 in Concurrency chapter here we have a strictly increasing monotonic state on y
                Because of the await operator we do not have interleaving *)
  );

*)

(*
printreduce(
  Assign("y",AwtPar( Seq(Assign("y", Integer 0 ),Assign("y", Op(Deref "y", ADD, Integer 1))))),
  [("y",0)] (* Here we have that y has always the value  = 1  *)
  );

*)
