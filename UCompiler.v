Require Vector.
Require Import List.
Import Vector.VectorNotations.

(* HELPER FUNCTIONS *)

(* List.In as a Type (not Prop) *)
Inductive InT {A} (a : A) : list A -> Type :=
| InT_eq {l} : InT a (cons a l)
| InT_cons {b l} (i : InT a l) : InT a (cons b l).

(* Fin.t index of element InT *)
Fixpoint getFin {A a l} (i : @InT A a l) : Fin.t (length l) :=
  match i with
  | InT_eq _ => Fin.F1
  | InT_cons _ i => Fin.FS (getFin i)
  end.

(* TODOC *)
Fixpoint rep {A n} (a : A) : Vector.t A n :=
  match n with
  | 0 => []
  | S n' => a :: rep a
  end.

(* build a Vector.t from a function on its Fin.t indices *)
Fixpoint build {A n} (f : Fin.t n -> A) : Vector.t A n :=
  match n as n return (Fin.t n -> A) -> Vector.t A n with
  | 0 => fun _ => []
  | S n' => fun f => f Fin.F1 :: build (fun p => f (Fin.FS p))
  end f.

(* destruct a Fin.t (m + n) into a Fin.t m or Fin.t n *)
Fixpoint FinLR {m n} (p : Fin.t (m + n)) : Fin.t m + Fin.t n :=
  match m as m return Fin.t (m + n) -> Fin.t m + Fin.t n with
  | 0 => fun p => inr p
  | S m' => fun p => match p with
                     | Fin.F1 => fun _ => inl Fin.F1
                     | Fin.FS p' => fun FinLR => match FinLR p' with
                                                 | inl pm => inl (Fin.FS pm)
                                                 | inr pn => inr pn
                                                 end
                     end FinLR
  end p.

Notation FinL := (Fin.L _).
Notation FinR := (Fin.R _).
Notation Fin1 := Fin.F1.
Notation Fin2 := (Fin.FS Fin.F1).

(* TODO:
   - type system with complex types
       (currently each value is only two wires: a data bit and an abort bit)
   - let-expr in value
   - let-expr in action
   - let-expr in comb_circuit (to be used instead of copying circuits all over the place)
   - arbitrary functions in value
   - read/write ports
   - inputs to value methods
       (including the need for a mechanism to ensure that each value method is called only once)
   - multiple inputs to action methods
   - mechanism preventing value method calls from violating ORAAT semantics
       (currently value method calls do not consider previously completed actions)
   - mechanism preventing aborting action method calls from violating ORAAT semantics
       (currently we do calculate when an action aborts, but we have yet to use that to
        appropariately abort an entire rule or action method)
   - allow for arbitrary interleaving of value methods, rules, and action methods
       (currently they are always scheduled in the order listed above)
*)

Section Lang.

Context {reg_T mod_name_T met_name_T var_T : Type}.

(* COMBINATIONAL CIRCUIT *)

(* a combinational circuit with I input wires and O output wires *)
Inductive comb_circuit (I O : nat) : Type :=
| cc_out (o : Vector.t (Fin.t I) O)
| cc_bool (b : bool) (tl : comb_circuit (I + 1) O)
| cc_not (i : Fin.t I) (tl : comb_circuit (I + 1) O)
| cc_and (in1 in2 : Fin.t I) (tl : comb_circuit (I + 1) O)
| cc_or (in1 in2 : Fin.t I) (tl : comb_circuit (I + 1) O)
| cc_mux (sel tru fal : Fin.t I) (tl : comb_circuit (I + 1) O).
Arguments cc_out {I O}.
Arguments cc_bool {I O}.
Arguments cc_not {I O}.
Arguments cc_and {I O}.
Arguments cc_or {I O}.
Arguments cc_mux {I O}.

(* TODOC *)
Definition fmap1 {I I'} (f : Fin.t I -> Fin.t I') : Fin.t (I + 1) -> Fin.t (I' + 1) :=
  fun p => match FinLR p with
           | inl pI => FinL (f pI)
           | inr p1 => FinR p1
           end.

(* TODOC *)
Fixpoint cc_map {I I' O} (f : Fin.t I -> Fin.t I') (cc : comb_circuit I O) : comb_circuit I' O :=
  match cc with
  | cc_out o => cc_out (Vector.map f o)
  | cc_bool b tl => cc_bool b (cc_map (fmap1 f) tl)
  | cc_not i tl => cc_not (f i) (cc_map (fmap1 f) tl)
  | cc_and in1 in2 tl => cc_and (f in1) (f in2) (cc_map (fmap1 f) tl)
  | cc_or in1 in2 tl => cc_or (f in1) (f in2) (cc_map (fmap1 f) tl)
  | cc_mux sel tru fal tl => cc_mux (f sel) (f tru) (f fal) (cc_map (fmap1 f) tl)
  end.

(* TODOC *)
Fixpoint cc_connect {I N O} (cc1 : comb_circuit I N) (cc2 : comb_circuit N O)
  : comb_circuit I O :=
  match cc1 with
  | cc_out o => cc_map (Vector.nth o) cc2
  | cc_bool b tl => cc_bool b (cc_connect tl cc2)
  | cc_not i tl => cc_not i (cc_connect tl cc2)
  | cc_and in1 in2 tl => cc_and in1 in2 (cc_connect tl cc2)
  | cc_or in1 in2 tl => cc_or in1 in2 (cc_connect tl cc2)
  | cc_mux sel tru fal tl => cc_mux sel tru fal (cc_connect tl cc2)
  end.

(* TODOC
   TODO: make this more efficient by only mapping over o once at the end *)
Fixpoint cc_app {I O O'} (o : Vector.t (Fin.t I) O) (cc : comb_circuit I O')
  : comb_circuit I (O + O') :=
  match cc with
  | cc_out o' => cc_out (o ++ o')
  | cc_bool b tl => cc_bool b (cc_app (Vector.map FinL o) tl)
  | cc_not i tl => cc_not i (cc_app (Vector.map FinL o) tl)
  | cc_and in1 in2 tl => cc_and in1 in2 (cc_app (Vector.map FinL o) tl)
  | cc_or in1 in2 tl => cc_or in1 in2 (cc_app (Vector.map FinL o) tl)
  | cc_mux sel tru fal tl => cc_mux sel tru fal (cc_app (Vector.map FinL o) tl)
  end.

(* TODOC
   TODO: make this more iefficient by only mapping over cc2 once at the end *)
Fixpoint cc_pair {I O1 O2} (cc1 : comb_circuit I O1) (cc2 : comb_circuit I O2)
  : comb_circuit I (O1 + O2) :=
  match cc1 with
  | cc_out o => cc_app o cc2
  | cc_bool b tl => cc_bool b (cc_pair tl (cc_map FinL cc2))
  | cc_not i tl => cc_not i (cc_pair tl (cc_map FinL cc2))
  | cc_and in1 in2 tl => cc_and in1 in2 (cc_pair tl (cc_map FinL cc2))
  | cc_or in1 in2 tl => cc_or in1 in2 (cc_pair tl (cc_map FinL cc2))
  | cc_mux sel tru fal tl => cc_mux sel tru fal (cc_pair tl (cc_map FinL cc2))
  end.

(* TODOC *)
Definition flet {I O} (o : Vector.t (Fin.t I) O) : Fin.t (I + O) -> Fin.t I :=
  fun p => match FinLR p with
           | inl pI => pI
           | inr pO => Vector.nth o pO
           end.

(* TODOC *)
Definition flet1 {I O} : Fin.t (I + O) -> Fin.t ((I + 1) + O) :=
  fun p => match FinLR p with
           | inl pI => FinL (FinL pI)
           | inr pO => FinR pO
           end.

(* TODOC
   TODO: make this more efficient by only mapping over cc_body once at the end *)
Fixpoint cc_let {I O O'} (cc_expr : comb_circuit I O) (cc_body : comb_circuit (I + O) O')
  : comb_circuit I O' :=
  match cc_expr with
  | cc_out o => cc_map (flet o) cc_body
  | cc_bool b tl => cc_bool b (cc_let tl (cc_map flet1 cc_body))
  | cc_not i tl => cc_not i (cc_let tl (cc_map flet1 cc_body))
  | cc_and in1 in2 tl => cc_and in1 in2 (cc_let tl (cc_map flet1 cc_body))
  | cc_or in1 in2 tl => cc_or in1 in2 (cc_let tl (cc_map flet1 cc_body))
  | cc_mux sel tru fal tl => cc_mux sel tru fal (cc_let tl (cc_map flet1 cc_body))
  end.

(* VALUE *)

(* a language value *)
Inductive value (sig : list var_T) (R : list reg_T) (V : list (mod_name_T * met_name_T))
  : Type :=
| v_bool (b : bool)
| v_not (v : value sig R V)
| v_and (v1 v2 : value sig R V)
| v_or (v1 v2 : value sig R V)
| v_if (c t f : value sig R V)
| v_var {x : var_T} (i : InT x sig)
| v_read {r : reg_T} (i : InT r R)
| v_call {M : mod_name_T} {m : met_name_T} (i : InT (M, m) V)
| v_abort.
Arguments v_bool {sig R V}.
Arguments v_not {sig R V}.
Arguments v_and {sig R V}.
Arguments v_or {sig R V}.
Arguments v_if {sig R V}.
Arguments v_var {sig R V x}.
Arguments v_read {sig R V r}.
Arguments v_call {sig R V M m}.
Arguments v_abort {sig R V}.

(* circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   circuit outputs:
   - 1 = data wire of value
   - 2 = whether or not value aborts *)
Fixpoint compile_value {sig R V} (v : value sig R V)
  : comb_circuit (length sig + (length R + length R) + (length V + length V)) 2 :=
  match v with
  | v_bool b => match b with
                | true => cc_bool true (cc_bool false (cc_out [FinL (FinR Fin1); FinR Fin1]))
                | false => cc_bool false (cc_out [FinR Fin1; FinR Fin1])
                end
  | v_not v => cc_connect (compile_value v) (cc_not Fin1 (cc_out [FinR Fin1; FinL Fin2]))
  | v_and v1 v2 => cc_connect (* N = 2 + 2 *)
                     (cc_pair (compile_value v1) (compile_value v2))
                     (cc_pair
                        (cc_and (FinL Fin1) (FinR Fin1) (cc_out [FinR Fin1])) (* data *)
                        (cc_or (FinL Fin2) (FinR Fin2) (cc_out [FinR Fin1]))) (* abort *)
  | v_or v1 v2 => cc_connect (* N = 2 + 2 *)
                    (cc_pair (compile_value v1) (compile_value v2))
                    (cc_pair
                       (cc_or (FinL Fin1) (FinR Fin1) (cc_out [FinR Fin1])) (* data *)
                       (cc_or (FinL Fin2) (FinR Fin2) (cc_out [FinR Fin1]))) (* abort *)
  | v_if c t f => cc_connect (* N = 2 + (2 + 2) *)
                    (cc_pair (compile_value c) (cc_pair (compile_value t) (compile_value f)))
                    (cc_pair
                       (cc_mux (FinL Fin1) (FinR (FinL Fin1)) (FinR (FinR Fin1)) (* data *)
                          (cc_out [FinR Fin1]))
                       (cc_mux (FinL Fin1) (FinR (FinL Fin2)) (FinR (FinR Fin2)) (* abort *)
                          (cc_or (FinL (FinL Fin2)) (FinR Fin1) (cc_out [FinR Fin1]))))
  | v_var i => cc_bool false (cc_out [FinL (FinL (FinL (getFin i))); FinR Fin1])
  | v_read i => cc_out [FinL (FinR (FinL (getFin i))); FinL (FinR (FinR (getFin i)))]
  | v_call i => cc_out [FinR (FinL (getFin i)); FinR (FinR (getFin i))]
  | v_abort => cc_bool false (cc_out [FinR Fin1; FinR Fin1])
  end.

(* ACTION *)

(* a language action *)
Inductive action (sig : list var_T) (R : list reg_T) (V A : list (mod_name_T * met_name_T))
  : Type :=
| a_done
| a_par (l r : action sig R V A)
| a_if (c : value sig R V) (t f : action sig R V A)
| a_write {r : reg_T} (i : InT r R) (arg : value sig R V)
| a_call {M : mod_name_T} {m : met_name_T} (i : InT (M, m) A) (arg : value sig R V)
| a_abort.
Arguments a_done {sig R V A}.
Arguments a_par {sig R V A}.
Arguments a_if {sig R V A}.
Arguments a_write {sig R V A r}.
Arguments a_call {sig R V A M m}.
Arguments a_abort {sig R V A}.

(* circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   - length A + length A = action method already-called wires + abort wires
   circuit outputs:
   - 1 = whether or not action a aborts based on values or self-abort
   - length R = whether or not action a wants to write to each register
   - length R = data action a would write to each register
   - length R = whether or not action a aborts based on multiple writes to each register
                note to prove: multi-write abort always implies want for each register
   - length A = whether or not action a wants to call each action method
   - length A = data action a would send as argument to each action method
   - length A = whether or not action a aborts based on multiple calls to each action method
                note to prove: multi-call abort always implies want for each action method *)
Fixpoint compile_action {sig R V A} (a : action sig R V A)
  : comb_circuit
      (length sig + (length R + length R) + (length V + length V) + (length A + length A))
      (1 + ((length R + length R + length R) + (length A + length A + length A))) :=
  match a with
  | a_done => cc_bool false (cc_out (rep (FinR Fin1)))
  | a_par l r => cc_connect (* N = (1 + (RRR + AAA)) + (1 + (RRR + AAA)) *)
                   (cc_pair (compile_action l) (compile_action r))
                   (cc_pair
                      (cc_or (FinL (FinL Fin1)) (FinR (FinL Fin1)) (cc_out [FinR Fin1]))
                      (cc_pair (* RRR + AAA *) 
                         (cc_pair (* RRR *)
                            (cc_pair
                               (build (fun r => cc_or
                                                  (FinL (FinR (FinL (FinL (FinL r)))))
                                                  (FinR (FinR (FinL (FinL (FinL r)))))
                                                  (cc_out [FinR Fin1])))
                               (build (fun r => cc_mux
                                                  (FinL (FinR (FinL (FinL (FinL r)))))
                                                  (FinL (FinR (FinL (FinL (FinR r)))))
                                                  (FinR (FinR (FinL (FinL (FinR r)))))
                                                  (cc_out [FinR Fin1]))))
                            (build (fun r => cc_and
                                               (FinL (FinR (FinL (FinL (FinL r)))))
                                               (FinR (FinR (FinL (FinL (FinL r)))))
                                               (cc_or
                                                  (FinL (FinL (FinR (FinL (FinR r)))))
                                                  (FinL (FinR (FinR (FinL (FinR r)))))
                                                  (cc_or (FinL (FinR Fin1)) (FinR Fin1)
                                                     (cc_out [FinR Fin1]))))))
                         (cc_pair (* AAA *)
                            (cc_pair
                               _
                               _)
                            _)))
  | a_if c t f => cc_connect (* N = 2 + ((1 + (RRR + AAA)) + (1 + (RRR + AAA))) *)
                    (cc_pair
                       (cc_map FinL (compile_value c))
                       (cc_pair (compile_action t) (compile_action f)))
                    (cc_pair
                       (cc_mux (FinL Fin1) (FinR (FinL (FinL Fin1))) (FinR (FinR (FinL Fin1)))
                          (cc_or (FinL (FinL Fin2)) (FinR Fin1) (cc_out [FinR Fin1])))
                       (cc_pair (* RRR + AAA *)
                          (cc_pair (* RRR *)
                             (cc_pair
                                _
                                _)
                             _)
                          (cc_pair (* AAA *)
                             (cc_pair
                                _
                                _)
                             _)))
  | a_write _ arg => cc_let (* I + O = (lengthsig + RR + VV + AA) + 2 *)
                       (cc_map FinL (compile_value arg))
                       (cc_pair
                          (cc_out [FinR Fin2])
                          (cc_pair (* RRR + AAA *)
                             (cc_pair (* RRR *)
                                (cc_pair
                                   _
                                   _)
                                _)
                             (cc_pair (* AAA *)
                                (cc_pair
                                   _
                                   _)
                                _)))
  | a_call _ arg => cc_let (* I + O = (lengthsig + RR + VV + AA) + 2 *)
                      (cc_map FinL (compile_value arg))
                      (cc_pair
                         (cc_out [FinR Fin2])
                         (cc_pair (* RRR + AAA *)
                            (cc_pair (* RRR *)
                               (cc_pair
                                  _
                                  _)
                               _)
                            (cc_pair (* AAA *)
                               (cc_pair
                                  _
                                  _)
                               _)))
  | a_abort => cc_bool true (cc_bool false (cc_out (FinL (FinR Fin1) :: rep (FinR Fin1))))
  end.

(* whether or not action a aborts based on values or self-abort
   circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   - length A + length A = action method already-called wires + abort wires *)
Fixpoint compile_action_vsabort {sig R V A} (a : action sig R V A)
  : comb_circuit
      (length sig + (length R + length R) + (length V + length V) + (length A + length A)) :=
  let F := cc_connect (fun i => cc_input (Fin.L _ i)) in
  match a with
  | a_done => cc_bool false
  | a_par l r => cc_or (compile_action_vsabort l) (compile_action_vsabort r)
  | a_if c t f => cc_or (F (compile_value_abort c))
                    (cc_mux (F (compile_value_data c))
                       (compile_action_vsabort t) (compile_action_vsabort f))
  | a_write _ arg => F (compile_value_abort arg)
  | a_call _ arg => F (compile_value_abort arg)
  | a_abort => cc_bool true
  end.

(* wire 1 = whether or not action a wants to write to pth register
   wire 2 = data action a would write to pth register
   wire 3 = whether or not action a aborts based on multiple writes to pth register
   note to prove: wire 3 always implies wire 1
   circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   - length A + length A = action method already-called wires + abort wires *)
Fixpoint compile_action_write {sig R V A} (a : action sig R V A) (p : Fin.t (length R))
  : comb_circuit
      (length sig + (length R + length R) + (length V + length V) + (length A + length A))
    * comb_circuit
        (length sig + (length R + length R) + (length V + length V) + (length A + length A))
    * comb_circuit
        (length sig + (length R + length R) + (length V + length V) + (length A + length A)) :=
  let F := cc_connect (fun i => cc_input (Fin.L _ i)) in
  match a with
  | a_done => (cc_bool false, cc_bool false, cc_bool false)
  | a_par l r => match compile_action_write l p, compile_action_write r p with
                 | (ctrl_l, data_l, abort_l), (ctrl_r, data_r, abort_r) =>
                     (cc_or ctrl_l ctrl_r, cc_mux ctrl_l data_l data_r,
                       cc_or (cc_and ctrl_l ctrl_r) (cc_or abort_l abort_r))
                 end
  | a_if c t f => match compile_action_write t p, compile_action_write f p with
                  | (ctrl_t, data_t, abort_t), (ctrl_f, data_f, abort_f) =>
                      (cc_or (cc_and (F (compile_value_data c)) ctrl_t)
                         (cc_and (cc_not (F (compile_value_data c))) ctrl_f),
                        cc_mux (F (compile_value_data c)) data_t data_f,
                        cc_or (cc_and (F (compile_value_data c)) abort_t)
                         (cc_and (cc_not (F (compile_value_data c))) abort_f))
                  end
  | a_write i arg => if Fin.eqb p (getFin i)
                     then (cc_bool true, F (compile_value_data arg),
                            cc_input (Fin.L _ (Fin.L _ (Fin.R _ (Fin.R _ p)))))
                     else (cc_bool false, cc_bool false, cc_bool false)
  | a_call _ _ => (cc_bool false, cc_bool false, cc_bool false)
  | a_abort => (cc_bool false, cc_bool false, cc_bool false)
  end.

(* wire 1 = whether or not action a wants to call pth action method
   wire 2 = data action a would send as argument to pth action method
   wire 3 = whether or not action a aborts based on multiple calls to pth action method
   note to prove: wire 3 always implies wire 1
   circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   - length A + length A = action method already-called wires + abort wires *)
Fixpoint compile_action_call {sig R V A} (a : action sig R V A) (p : Fin.t (length A))
  : comb_circuit
      (length sig + (length R + length R) + (length V + length V) + (length A + length A))
    * comb_circuit
        (length sig + (length R + length R) + (length V + length V) + (length A + length A))
    * comb_circuit
        (length sig + (length R + length R) + (length V + length V) + (length A + length A)) :=
  let F := cc_connect (fun i => cc_input (Fin.L _ i)) in
  match a with
  | a_done => (cc_bool false, cc_bool false, cc_bool false)
  | a_par l r => match compile_action_call l p, compile_action_call r p with
                 | (ctrl_l, data_l, abort_l), (ctrl_r, data_r, abort_r) =>
                     (cc_or ctrl_l ctrl_r, cc_mux ctrl_l data_l data_r,
                       cc_or (cc_and ctrl_l ctrl_r) (cc_or abort_l abort_r))
                 end
  | a_if c t f => match compile_action_call t p, compile_action_call f p with
                  | (ctrl_t, data_t, abort_t), (ctrl_f, data_f, abort_f) =>
                      (cc_or (cc_and (F (compile_value_data c)) ctrl_t)
                         (cc_and (cc_not (F (compile_value_data c))) ctrl_f),
                        cc_mux (F (compile_value_data c)) data_t data_f,
                        cc_or (cc_and (F (compile_value_data c)) abort_t)
                         (cc_and (cc_not (F (compile_value_data c))) abort_f))
                  end
  | a_write _ _ => (cc_bool false, cc_bool false, cc_bool false)
  | a_call i arg => if Fin.eqb p (getFin i)
                    then (cc_bool true, F (compile_value_data arg),
                           cc_input (Fin.R _ (Fin.L _ p)))
                    else (cc_bool false, cc_bool false, cc_bool false)
  | a_abort => (cc_bool false, cc_bool false, cc_bool false)
  end.

(* whether or not action a aborts based on values, self-abort, multiple writes to the same
   register, or multiple calls to the same action method
   circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   - length A + length A = action method already-called wires + abort wires *)
Definition compile_action_preabort {sig R V A} (a : action sig R V A)
  : comb_circuit
      (length sig + (length R + length R) + (length V + length V) + (length A + length A)) :=
  cc_or (compile_action_vsabort a)
    (cc_or
       (Vector.fold_right (fun bits => match bits with
                                       | (_, _, cc_abort) => cc_or cc_abort
                                       end) (build (compile_action_write a)) (cc_bool false))
       (Vector.fold_right (fun bits => match bits with
                                       | (_, _, cc_abort) => cc_or cc_abort
                                       end) (build (compile_action_call a)) (cc_bool false))).

(* whether or not action a is selected to write to register p
   circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   - length A + length A = action method already-called wires + abort wires *)
Definition compile_action_write_sel {sig R V A} (a : action sig R V A) (p : Fin.t (length R))
  : comb_circuit
      (length sig + (length R + length R) + (length V + length V) + (length A + length A)) :=
  match compile_action_write a p with
  | (cc_want, _, _) => cc_and cc_want (cc_not (compile_action_preabort a))
  end.

(* data action a would write to register p
   circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   - length A + length A = action method already-called wires + abort wires *)
Definition compile_action_write_data {sig R V A} (a : action sig R V A) (p : Fin.t (length R))
  : comb_circuit
      (length sig + (length R + length R) + (length V + length V) + (length A + length A)) :=
  match compile_action_write a p with
  | (_, cc_data, _) => cc_data
  end.

(* whether or not action a is selected to call action method p
   circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   - length A + length A = action method already-called wires + abort wires *)
Definition compile_action_call_sel {sig R V A} (a : action sig R V A) (p : Fin.t (length A))
  : comb_circuit
      (length sig + (length R + length R) + (length V + length V) + (length A + length A)) :=
  match compile_action_call a p with
  | (cc_want, _, _) => cc_and cc_want (cc_not (compile_action_preabort a))
  end.

(* data action a would send to action method p
   circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   - length A + length A = action method already-called wires + abort wires *)
Definition compile_action_call_data {sig R V A} (a : action sig R V A) (p : Fin.t (length A))
  : comb_circuit
      (length sig + (length R + length R) + (length V + length V) + (length A + length A)) :=
  match compile_action_call a p with
  | (_, cc_data, _) => cc_data
  end.

(* whether or not action a aborts
   circuit inputs:
   - length sig = action method input data wires
   - length R + length R = register read data wires + already-written-to wires
   - length V + length V = value method data wires + abort wires
   - length A + length A = action method already-called wires + abort wires
   still need to use this function appropriately  *)
Definition compile_action_abort {sig R V A} (a : action sig R V A)
  : comb_circuit
      (length sig + (length R + length R) + (length V + length V) + (length A + length A)) :=
  cc_or (compile_action_preabort a)
    (Vector.fold_right cc_or
       (build (fun p => cc_and (compile_action_call_sel a p) (cc_input (Fin.R _ (Fin.R _ p)))))
       (cc_bool false)).

(* VALUE METHOD *)

(* a language value method *)
Record value_method R V : Type :=
  mkvm {
      name_vm : met_name_T;
      body_vm : value [] R V;
    }.
Arguments name_vm {R V}.
Arguments body_vm {R V}.

(* function to be used with cc_connect
   old circuit inputs:
   - lengthR + lengthR = register read data wires + already-written-to wires
   - lengthV + lengthV = children value method data wires + abort wires
   new circuit inputs:
   - lengthR = register read data wires
   - lengthV + lengthV = children value method data wires + abort wires *)
Definition connect_value_method {lengthR lengthV}
  (i : Fin.t ((lengthR + lengthR) + (lengthV + lengthV)))
  : comb_circuit (lengthR + (lengthV + lengthV)) :=
  match LR i with
  | inl iRR => match LR iRR with
               | inl iR => cc_input (Fin.L _ iR)
               | inr iR => cc_bool false
               end
  | inr iVV => cc_input (Fin.R _ iVV)
  end.

(* data wire of value method
   circuit inputs:
   - length R = register read data wires
   - length V + length V = children value method data wires + abort wires *)
Definition compile_value_method_data {R V} (vm : value_method R V)
  : comb_circuit (length R + (length V + length V)) :=
  cc_connect connect_value_method (compile_value_data (body_vm vm)).

(* whether or not value method aborts
   circuit inputs:
   - length R = register read data wires
   - length V + length V = children value method data wires + abort wires *)
Definition compile_value_method_abort {R V} (vm : value_method R V)
  : comb_circuit (length R + (length V + length V)) :=
  cc_connect connect_value_method (compile_value_abort (body_vm vm)).

(* SCHEDULE... *)

(* For now, schedule assumes all value methods are offered to parent first, then all rules are
     attempted to be executed, then all action methods are offered.
   In the final sequential circuit, we separate value method circuits from rules & action method
     circuits. So here, schedule is only used for iteratively compiling rules & action methods *)

(* a schedule is a collection of combinational circuits to which rules and action methods are
     compiled
   circuit inputs:
   - acts + acts = action method enable wires + argument data wires
       (acts grows as action methods are added to the schedule)
       (it is assumed that parent won't enable action method if argument was abort, hence we
        don't take action method abort wires as input)
   - lengthR + lengthR = register read data wires + already-written-to wires
   - VV = children value method data wires + abort wires
   - lengthR = register write data wires
   - lengthA + lengthA = children action method enable wires + argument data wires
   circuit outputs:
   - write_used = whether or not schedule writes to each register
   - write_data = data to be written to each register
   - call_enable = whether or not schedule calls each child action method
   - call_data = data to be sent as argument to each child action method *)
Record schedule acts lengthR VV lengthA : Type :=
  mks {
      write_used
      : Vector.t (comb_circuit ((acts + acts) + (lengthR + lengthR) + VV
                                + (lengthR + (lengthA + lengthA)))) lengthR;
      write_data
      : Vector.t (comb_circuit ((acts + acts) + (lengthR + lengthR) + VV
                                + (lengthR + (lengthA + lengthA)))) lengthR;
      call_enable
      : Vector.t (comb_circuit ((acts + acts) + (lengthR + lengthR) + VV
                                + (lengthR + (lengthA + lengthA)))) lengthA;
      call_data
      : Vector.t (comb_circuit ((acts + acts) + (lengthR + lengthR) + VV
                                + (lengthR + (lengthA + lengthA)))) lengthA;
    }.
Arguments write_used {acts lengthR VV lengthA}.
Arguments write_data {acts lengthR VV lengthA}.
Arguments call_enable {acts lengthR VV lengthA}.
Arguments call_data {acts lengthR VV lengthA}.

(* empty schedule
   write_used = input reg already written to
   write_data = if reg already written to, then write data else read data
   call_enable = input child action method enable
   call_data = input child action method argument data *)
Definition nil_schedule {acts lengthR VV lengthA} : schedule acts lengthR VV lengthA :=
  mks _ _ _ _
    (build (fun p => cc_input (Fin.L _ (Fin.L _ (Fin.R _ (Fin.R _ p))))))
    (build (fun p => cc_mux (cc_input (Fin.L _ (Fin.L _ (Fin.R _ (Fin.R _ p)))))
                       (cc_input (Fin.R _ (Fin.L _ p)))
                       (cc_input (Fin.L _ (Fin.L _ (Fin.R _ (Fin.L _ p)))))))
    (build (fun p => cc_input (Fin.R _ (Fin.R _ (Fin.L _ p)))))
    (build (fun p => cc_input (Fin.R _ (Fin.R _ (Fin.R _ p))))).

(* function to be used with cc_connect
   adds an action method enable wire and argument data wire to acts
     (sig = 0 when action being added is a rule)
     (sig = 1 when action being added is an action method)
   connects outputs of s to i *)
Definition connect_schedule {sig acts lengthR VV lengthA}
  (s : schedule (sig + acts) lengthR VV lengthA)
  (i : Fin.t ((acts + acts) + (lengthR + lengthR) + VV + (lengthR + (lengthA + lengthA))))
  : comb_circuit (((sig + acts) + (sig + acts)) + (lengthR + lengthR) + VV
                  + (lengthR + (lengthA + lengthA))) :=
  match LR i with
  | inl iaaRRVV =>
      match LR iaaRRVV with
      | inl iaaRR =>
          match LR iaaRR with
          | inl iaa => match LR iaa with
                       | inl ia => cc_input (Fin.L _ (Fin.L _ (Fin.L _ (Fin.L _ (Fin.R _ ia)))))
                       | inr ia => cc_input (Fin.L _ (Fin.L _ (Fin.L _ (Fin.R _ (Fin.R _ ia)))))
                       end
          | inr iRR => match LR iRR with
                       | inl iR => cc_input (Fin.L _ (Fin.L _ (Fin.R _ (Fin.L _ iR))))
                       | inr iR => Vector.nth (write_used s) iR
                       end
          end
      | inr iVV => cc_input (Fin.L _ (Fin.R _ iVV))
      end
  | inr iRAA => match LR iRAA with
                | inl iR => Vector.nth (write_data s) iR
                | inr iAA => match LR iAA with
                             | inl iA => Vector.nth (call_enable s) iA
                             | inr iA => Vector.nth (call_data s) iA
                             end
                end
  end.

(* appends two schedules together *)
Definition cons_schedule {sig acts lengthR VV lengthA}
  (s1 : schedule (sig + acts) lengthR VV lengthA) (s2 : schedule acts lengthR VV lengthA)
  : schedule (sig + acts) lengthR VV lengthA :=
  mks _ _ _ _
    (Vector.map (cc_connect (connect_schedule s1)) (write_used s2))
    (Vector.map (cc_connect (connect_schedule s1)) (write_data s2))
    (Vector.map (cc_connect (connect_schedule s1)) (call_enable s2))
    (Vector.map (cc_connect (connect_schedule s1)) (call_data s2)).

(* function to be used with cc_connect
   old circuit inputs:
   - sig = action argument data wire
   - lengthR + lengthR = register read data wires + already-written-to wires
   - VV = children value method data wires + abort wires
   - lengthA + lengthA = children action method already-called wires + abort wires
   new circuit inputs:
   - sig + sig = added action method enable wire and argument data wire
       (sig = 0 when action being added is a rule)
       (sig = 1 when action being added is an action method)
   - acts + acts = previous action method enable wires and argument data wires
   - lengthR + lengthR = register read data wires + already-written-to wires
   - VV = children value method data wires + abort wires
   - lengthR = register write data wires
   - lengthA + lengthA = children action method enable wires + argument data wires *)
Definition connect_action {sig acts RR VV lengthR lengthA}
  (i : Fin.t (sig + RR + VV + (lengthA + lengthA)))
  : comb_circuit (((sig + acts) + (sig + acts)) + RR + VV + (lengthR + (lengthA + lengthA))) :=
  match LR i with
  | inl isigRRVV =>
      match LR isigRRVV with
      | inl isigRR =>
          match LR isigRR with
          | inl isig => cc_input (Fin.L _ (Fin.L _ (Fin.L _ (Fin.R _ (Fin.L _ isig)))))
          | inr iRR => cc_input (Fin.L _ (Fin.L _ (Fin.R _ iRR)))
          end
      | inr iVV => cc_input (Fin.L _ (Fin.R _ iVV))
      end
  | inr iAA => match LR iAA with
               | inl iA => cc_input (Fin.R _ (Fin.R _ (Fin.L _ iA)))
               | inr iA => cc_bool false (* TODO: use children action method aborts *)
               end
  end.

(* RULE *)

(* a language rule *)
Definition rule R V A : Type := action [] R V A.

(* adds rule to beginning of schedule *)
Definition compile_rule {acts R V A} (r : rule R V A)
  (s : schedule acts (length R) (length V + length V) (length A))
  : schedule acts (length R) (length V + length V) (length A) :=
  cons_schedule
    (mks _ _ _ _
       (build (fun p => cc_or (cc_input (Fin.L _ (Fin.L _ (Fin.R _ (Fin.R _ p)))))
                          (cc_connect connect_action (compile_action_write_sel r p))))
       (build (fun p => cc_mux (cc_input (Fin.L _ (Fin.L _ (Fin.R _ (Fin.R _ p)))))
                          (cc_input (Fin.R _ (Fin.L _ p)))
                          (cc_connect connect_action (compile_action_write_data r p))))
       (build (fun p => cc_or (cc_input (Fin.R _ (Fin.R _ (Fin.L _ p))))
                          (cc_connect connect_action (compile_action_call_sel r p))))
       (build (fun p => cc_mux (cc_input (Fin.R _ (Fin.R _ (Fin.L _ p))))
                          (cc_input (Fin.R _ (Fin.R _ (Fin.R _ p))))
                          (cc_connect connect_action (compile_action_call_data r p)))))
    s.

(* ACTION METHOD *)

(* a language action method *)
Record action_method R V A : Type :=
  mkam {
    name_am : met_name_T;
    arg_am : var_T;
    body_am : action [arg_am] R V A;
    }.
Arguments name_am {R V A}.
Arguments arg_am {R V A}.
Arguments body_am {R V A}.

(* adds action method to beginning of schedule *)
Definition compile_action_method {acts R V A} (am : action_method R V A)
  (s : schedule acts (length R) (length V + length V) (length A))
  : schedule (S acts) (length R) (length V + length V) (length A) :=
  cons_schedule
    (mks _ _ _ _
       (build (fun p =>
                 cc_or (cc_input (Fin.L _ (Fin.L _ (Fin.R _ (Fin.R _ p)))))
                   (cc_and (* check enable *)
                      (cc_input (Fin.L _ (Fin.L _ (Fin.L _ (Fin.L _ (Fin.L _ Fin1))))))
                      (cc_connect connect_action (compile_action_write_sel (body_am am) p)))))
       (build (fun p =>
                 cc_mux (cc_input (Fin.L _ (Fin.L _ (Fin.R _ (Fin.R _ p)))))
                   (cc_input (Fin.R _ (Fin.L _ p)))
                   (cc_connect connect_action (compile_action_write_data (body_am am) p))))
       (build (fun p =>
                 cc_or (cc_input (Fin.R _ (Fin.R _ (Fin.L _ p))))
                   (cc_and (* check enable *)
                      (cc_input (Fin.L _ (Fin.L _ (Fin.L _ (Fin.L _ (Fin.L _ Fin1))))))
                      (cc_connect connect_action (compile_action_call_sel (body_am am) p)))))
       (build (fun p =>
                 cc_mux (cc_input (Fin.R _ (Fin.R _ (Fin.L _ p))))
                   (cc_input (Fin.R _ (Fin.R _ (Fin.R _ p))))
                   (cc_connect connect_action (compile_action_call_data (body_am am) p)))))
    s.

(* SEQUENTIAL CIRCUIT *)

(* a sequential circuit offering vals value methods and acts action methods *)
Record seq_circuit (vals acts : nat) : Type :=
  mksc {
      regs : nat;
      val_data : Vector.t (comb_circuit regs) vals;
      val_aborts : Vector.t (comb_circuit regs) vals;
      reg_writes : Vector.t (comb_circuit ((acts + acts) + regs)) regs; (* enables + arg data *)
      (* todo: input action method commits and output action method aborts *)
    }.

Definition cast {vals vals' acts acts'} (ev : vals = vals') (ea : acts = acts') :
  seq_circuit vals acts -> seq_circuit vals' acts' :=
  match ev, ea with eq_refl, eq_refl => fun sc => sc end.

Definition empty : seq_circuit 0 0 :=
  mksc 0 0 0 (Vector.nil _) (Vector.nil _) (Vector.nil _).

(* function to be used with cc_connect *)
Definition connect_group1 {a1 a2 regs1 regs2} (i : Fin.t ((a1 + a1) + regs1))
  : comb_circuit ((a1 + a2) + (a1 + a2) + (regs1 + regs2)) :=
  match LR i with
  | inl iaa => match LR iaa with
               | inl ia => cc_input (Fin.L _ (Fin.L _ (Fin.L _ ia)))
               | inr ia => cc_input (Fin.L _ (Fin.R _ (Fin.L _ ia)))
               end
  | inr ir => cc_input (Fin.R _ (Fin.L _ ir))
  end.

(* function to be used with cc_connect *)
Definition connect_group2 {a1 a2 regs1 regs2} (i : Fin.t ((a2 + a2) + regs2))
  : comb_circuit ((a1 + a2) + (a1 + a2) + (regs1 + regs2)) :=
  match LR i with
  | inl iaa => match LR iaa with
               | inl ia => cc_input (Fin.L _ (Fin.L _ (Fin.R _ ia)))
               | inr ia => cc_input (Fin.L _ (Fin.R _ (Fin.R _ ia)))
               end
  | inr ir => cc_input (Fin.R _ (Fin.R _ ir))
  end.

(* group disjoint (children) sequantial circuits together *)
Definition group {v1 v2 a1 a2} (c1 : seq_circuit v1 a1) (c2 : seq_circuit v2 a2)
  : seq_circuit (v1 + v2) (a1 + a2) :=
  mksc (v1 + v2) (a1 + a2) (regs _ _ c1 + regs _ _ c2)
    (Vector.append (Vector.map (cc_connect (fun p => cc_input (Fin.L _ p))) (val_data _ _ c1))
       (Vector.map (cc_connect (fun p => cc_input (Fin.R _ p))) (val_data _ _ c2)))
    (Vector.append (Vector.map (cc_connect (fun p => cc_input (Fin.L _ p))) (val_aborts _ _ c1))
       (Vector.map (cc_connect (fun p => cc_input (Fin.R _ p))) (val_aborts _ _ c2)))
    (Vector.append (Vector.map (cc_connect connect_group1) (reg_writes _ _ c1))
       (Vector.map (cc_connect connect_group2) (reg_writes _ _ c2))).

(* MODULE *)

(* a language module using children value methods V and children action methods A *)
Inductive module' V A : list met_name_T -> list met_name_T -> Type :=
| mk_mod (R : list reg_T) (vms : list (value_method R V)) (rules : list (rule R V A))
    (ams : list (action_method R V A))
  : module' V A (map name_vm vms) (map name_am ams)
| child_mod {vi ai vi' ai'} (M : mod_name_T) (mod : module' [] [] vi ai)
    (m' : module' (map (pair M) vi ++ V) (map (pair M) ai ++ A) vi' ai')
  : module' V A vi' ai'.
Arguments mk_mod {V A}.
Arguments child_mod {V A vi ai vi' ai'}.
Definition module := module' [] [].

(* adds list of action methods to schedule *)
Fixpoint compile_action_methods {R V A} (ams : list (action_method R V A))
  : schedule (length ams) (length R) (length V + length V) (length A) :=
  match ams with
  | [] => nil_schedule
  | am :: ams' => compile_action_method am (compile_action_methods ams')
  end.

(* builds schedule from listed rules and action methods *)
Definition build_schedule {R V A} (rules : list (rule R V A)) (ams : list (action_method R V A))
  : schedule (length ams) (length R) (length V + length V) (length A) :=
  fold_right compile_rule (compile_action_methods ams) rules.

(* function to be used with cc_connect *)
Definition connect_schedule' {acts lengthR lengthV lengthA}
  (children : seq_circuit lengthV lengthA)
  (i : Fin.t ((acts + acts) + (lengthR + lengthR) + (lengthV + lengthV)
              + (lengthR + (lengthA + lengthA))))
  : comb_circuit ((acts + acts) + (lengthR + regs _ _ children)) :=
  match LR i with
  | inl iaaRRVV =>
      match LR iaaRRVV with
      | inl iaaRR => match LR iaaRR with
                     | inl iaa => cc_input (Fin.L _ iaa)
                     | inr iRR => match LR iRR with
                                  | inl iR => cc_input (Fin.R _ (Fin.L _ iR))
                                  | inr iR => cc_bool false (* writes unused *)
                                  end
                     end
      | inr iVV =>
          match LR iVV with
          | inl iV => cc_connect (fun p => cc_input (Fin.R _ (Fin.R _ p)))
                        (Vector.nth (val_data _ _ children) iV)
          | inr iV => cc_connect (fun p => cc_input (Fin.R _ (Fin.R _ p)))
                        (Vector.nth (val_aborts _ _ children) iV)
          end
      end
  | inr iRAA => cc_bool false (* unused write data, calls not enables (yet), unused call arg *)
  end.

(* function to be used with cc_connect *)
Definition connect_children {acts lengthR lengthV lengthA}
  (s : schedule acts lengthR (lengthV + lengthV) lengthA)
  (children : seq_circuit lengthV lengthA)
  (i : Fin.t ((lengthA + lengthA) + regs _ _ children))
  : comb_circuit ((acts + acts) + (lengthR + regs _ _ children)) :=
  match LR i with
  | inl iaa => match LR iaa with
               | inl ia => cc_connect (connect_schedule' children)
                             (Vector.nth (call_enable s) ia)
               | inr ia => cc_connect (connect_schedule' children)
                             (Vector.nth (call_data s) ia)
               end
  | inr ir => cc_input (Fin.R _ (Fin.R _ ir))
  end.

(* combines children and schedule to make reg_writes of seq_circuit *)
Definition compile_schedule {acts lengthR lengthV lengthA}
  (children : seq_circuit lengthV lengthA)
  (s : schedule acts lengthR (lengthV + lengthV) lengthA)
  : Vector.t (comb_circuit ((acts + acts) + (lengthR + regs _ _ children)))
      (lengthR + regs _ _ children) :=
  Vector.append (Vector.map (cc_connect (connect_schedule' children)) (write_data s))
    (Vector.map (cc_connect (connect_children s children)) (reg_writes _ _ children)).

(* function to be used with cc_connect *)
Definition connect_value_method' {lengthR lengthV lengthA}
  (children : seq_circuit lengthV lengthA) (i : Fin.t (lengthR + (lengthV + lengthV)))
  : comb_circuit (lengthR + regs _ _ children) :=
  match LR i with
  | inl iR => cc_input (Fin.L _ iR)
  | inr iVV =>
      match LR iVV with
      | inl iV => cc_connect (fun p => cc_input (Fin.R _ p))
                    (Vector.nth (val_data _ _ children) iV)
      | inr iV => cc_connect (fun p => cc_input (Fin.R _ p))
                    (Vector.nth (val_aborts _ _ children) iV)
      end
  end.

(* compile module' *)
Fixpoint compile' {V A vi ai} (children : seq_circuit (length V) (length A))
  (m' : module' V A vi ai) : seq_circuit (length vi) (length ai) :=
  match m' in module' _ _ vi ai return seq_circuit (length vi) (length ai) with
  | mk_mod R vms rules ams =>
      cast eq_refl (eq_sym (map_length _ _))
        (mksc _ _ (length R + regs _ _ children)
           (Vector.cast (Vector.of_list
                           (map (fun vm => cc_connect (connect_value_method' children)
                                             (compile_value_method_data vm)) vms))
              (eq_trans (map_length _ _) (eq_sym (map_length _ _))))
           (Vector.cast (Vector.of_list
                           (map (fun vm => cc_connect (connect_value_method' children)
                                             (compile_value_method_abort vm)) vms))
              (eq_trans (map_length _ _) (eq_sym (map_length _ _))))
           (compile_schedule children (build_schedule rules ams)))
  | @child_mod _ _ vi' ai' _ _ M child m' =>
      @compile' (map (pair M) vi' ++ V) (map (pair M) ai' ++ A) _ _
        (cast
           (eq_trans (f_equal2 _ (eq_sym (map_length _ _)) eq_refl) (eq_sym (app_length _ _)))
           (eq_trans (f_equal2 _ (eq_sym (map_length _ _)) eq_refl) (eq_sym (app_length _ _)))
           (group (@compile' [] [] vi' ai' empty child) children)) m'
  end.

(* compile module *)
Definition compile {vi ai} (m : module vi ai) : seq_circuit (length vi) (length ai) :=
  @compile' [] [] vi ai empty m.

(* TODO: CIRCUIT INTERPRETER *)

(* old code

Fixpoint interpret' {W} (cc : comb_circuit W) : (Fin.t W -> bool) -> bool :=
  match cc in comb_circuit _ return (Fin.t W -> bool) -> bool with
  | const_cc _ b => fun _ => b
  | wire_cc _ w => fun B => B w
  | let_cc _ expr body =>
      fun B => interpret' body
                 (fun w => match w in Fin.t (S W) return (Fin.t W -> bool) -> bool -> bool with
                           | Fin1 => fun _ b => b
                           | Fin.FS f => fun B _ => B f
                           end B (interpret' expr B))
  | mux_cc _ sel tru fal => fun B => match interpret' sel B with
                            | true => interpret' tru B
                            | false => interpret' fal B
                            end
                                       
  end.

Definition interpret {v a} (c : circuit v a) : Vector.t bool v :=
  Vector.map (fun cc => interpret' cc (fun _ => false)) (cc _ _ c).
 *)

End Lang.

(* TODO: COMPILATION EXAMPLE(S) *)

(* old code

Require Import String.

Definition modT : module (reg_T:=string) (mod_name_T:=string) (var_T:=string) _ _ :=
  mk_mod [] [] [] [mkvm _ _ "vmT"%string (const_v _ _ true)] [] [].

Definition modF : module (reg_T:=string) (mod_name_T:=string) (var_T:=string) _ _ :=
  mk_mod [] [] [] [mkvm _ _ "vmF"%string (const_v _ _ false)] [] [].

Definition modTF : module _ _ :=
  child_mod _ _ "childT"%string modT
    (child_mod _ _ "childF"%string modF
       (mk_mod _ [] [] [mkvm _ _ "T"%string (call_v _ _ "childT"%string "vmT"%string
                                               (InT_cons _ (InT_eq _)));
                        mkvm _ _ "F"%string (call_v _ _ "childF"%string "vmF"%string
                                               (InT_eq _))] [] [])).

Compute (interpret (compile modTF)).



Definition modT2 : module (reg_T:=string) (mod_name_T:=string) (var_T:=string) _ _ :=
  mk_mod [] [] [] [mkvm _ _ "vmT"%string (let_v _ _ "x"%string (const_v _ _ true) (var_v _ _ "x"%string (InT_eq _)))] [] [].

Definition modF2 : module (reg_T:=string) (mod_name_T:=string) (var_T:=string) _ _ :=
  mk_mod [] [] [] [mkvm _ _ "vmF"%string (let_v _ _ "y"%string (const_v _ _ false) (var_v _ _ "y"%string (InT_eq _)))] [] [].

Definition modTF2 : module _ _ :=
  child_mod _ _ "childT"%string modT2
    (child_mod _ _ "childF"%string modF2
       (mk_mod _ [] [] [mkvm _ _ "T"%string (call_v _ _ "childT"%string "vmT"%string
                                               (InT_cons _ (InT_eq _)));
                        mkvm _ _ "F"%string (call_v _ _ "childF"%string "vmF"%string
                                               (InT_eq _))] [] [])).

Compute (interpret (compile modTF2)).
 *)

