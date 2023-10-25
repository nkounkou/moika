Require Vector.
Require Import List.
Import Vector.VectorNotations.

(* HELPER FUNCTIONS *)

(* List.In as a Type (not Prop) *)
Inductive InT {A} (a : A) : list A -> Type :=
| InT_eq {l} : InT a (cons a l)
| InT_cons {b l} (i : InT a l) : InT a (cons b l).

Definition seq_all n : Vector.t (Fin.t n) n.
  Admitted.

Context {var_T mod_name_T met_name_T : Type}.
Context {read write : met_name_T}.
Context {read0 read1 write0 write1 : met_name_T}.

(* LANGUAGE SYNTAX *)

(* TODO *)
Inductive const : nat -> Type :=
| k_nil : const 0
| k_bool : const 1.

(* TODO *)
Inductive func (sz sz' : nat) : Type.

Inductive value (Sig : list (var_T * nat))
  (M : list (mod_name_T * list (met_name_T * nat * nat + met_name_T * nat)))
  : nat -> Type :=
| v_const {sz} (k : const sz)
  : value Sig M sz
| v_func {sz sz'} (f : func sz sz') (arg : value Sig M sz)
  : value Sig M sz'
| v_if {sz} (c : value Sig M 1) (t f : value Sig M sz)
  : value Sig M sz
| v_var {x sz} (i : InT x Sig)
  : value Sig M sz
| v_let {x sz sz'} (expr : value Sig M sz) (body : value (cons (x, sz) Sig) M sz')
  : value Sig M sz
| v_call {m l n sz sz'} (i : InT (m, l) M) (i' : InT (inl (n, sz, sz')) l) (arg : value Sig M sz)
  : value Sig M sz'
| v_abort {sz}
  : value Sig M sz.
Arguments v_const {Sig M sz}.
Arguments v_func {Sig M sz sz'}.
Arguments v_if {Sig M sz}.
Arguments v_var {Sig M x sz}.
Arguments v_let {Sig M x sz sz'}.
Arguments v_call {Sig M m l n sz sz'}.
Arguments v_abort {Sig M sz}.

Inductive action (Sig : list (var_T * nat))
  (M : list (mod_name_T * list (met_name_T * nat * nat + met_name_T * nat)))
  : Type :=
| a_done
| a_par (l r : action Sig M)
| a_if (c : value Sig M 1) (t f : action Sig M)
| a_let {x sz} (expr : value Sig M sz) (body : action (cons (x, sz) Sig) M)
| a_call {m l n sz} (i : InT (m, l) M) (i' : InT (inr (n, sz)) l) (arg : value Sig M sz)
| a_abort.
Arguments a_done {Sig M}.
Arguments a_par {Sig M}.
Arguments a_if {Sig M}.
Arguments a_let {Sig M}.
Arguments a_call {Sig M m l n sz}.
Arguments a_abort {Sig M}.

Record value_method M : Type :=
  mkvm {
      name_vm : met_name_T;
      arg_vm : var_T * nat;
      sz_vm : nat;
      body_vm : value (cons arg_vm nil) M sz_vm;
    }.
Arguments name_vm {M}.
Arguments arg_vm {M}.
Arguments sz_vm {M}.
Arguments body_vm {M}.

Definition rule M : Type := action nil M.

Record action_method M : Type :=
  mkam {
      name_am : met_name_T;
      arg_am : var_T * nat;
      body_am : action (cons arg_am nil) M;
    }.
Arguments name_am {M}.
Arguments arg_am {M}.
Arguments body_am {M}.

Definition interface_reg sz : list (met_name_T * nat * nat + met_name_T * nat) :=
  cons (inl (read, 0, sz)) (cons (inr (write, sz)) nil).

Definition interface_ehr sz : list (met_name_T * nat * nat + met_name_T * nat) :=
  cons (inl (read0, 0, sz)) (cons (inr (write0, sz))
                               (cons (inl (read1, 0, sz)) (cons (inr (write1, sz)) nil))).

Fixpoint interface_top {M} (schedule : list (value_method M + rule M + action_method M))
  : list (met_name_T * nat * nat + met_name_T * nat) :=
  match schedule with
  | nil => nil
  | cons (inl (inl vm)) schedule' =>
      cons (inl (name_vm vm, snd (arg_vm vm), sz_vm vm)) (interface_top schedule')
  | cons (inl (inr _)) schedule' => interface_top schedule'
  | cons (inr am) schedule' =>
      cons (inr (name_am am, snd (arg_am am))) (interface_top schedule')
  end.

Inductive module' : list (mod_name_T * list (met_name_T * nat * nat + met_name_T * nat)) ->
                    list (met_name_T * nat * nat + met_name_T * nat) -> Type :=
| mod_reg (sz : nat)
  : module' nil (interface_reg sz)
| mod_ehr (sz : nat)
  : module' nil (interface_ehr sz)
| mod_top {M} (schedule : list (value_method M + rule M + action_method M))
  : module' M (interface_top schedule)
| mod_sub {M l l'} (m : mod_name_T) (sub : module' nil l) (m' : module' (cons (m, l) M) l')
  : module' M l'.
Arguments mod_top {M}.
Arguments mod_sub {M l l'}.
Definition module := module' nil.

(* CIRCUIT SYNTAX *)

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

Fixpoint input (mets : list (nat * nat + nat)) : nat :=
  match mets with
  | nil => 0
  | cons (inl (sz, _)) mets' => (1 + sz) + input mets'
  | cons (inr sz) mets' => (1 + sz + 1) + input mets'
  end.

Fixpoint output (mets : list (nat * nat + nat)) : nat :=
  match mets with
  | nil => 0
  | cons (inl (_, sz)) mets' => (sz + 1) + output mets'
  | cons (inr _) mets' => 1 + output mets'
  end.

Record seq_circuit (mets : list (nat * nat + nat)) : Type :=
  mksc {
      regs_sc : nat;
      cc_sc : comb_circuit (input mets + regs_sc) (regs_sc + output mets);
    }.
Arguments mksc {mets}.
Arguments regs_sc {mets}.
Arguments cc_sc {mets}.

(* CIRCUIT DEFINITIONS *)

Definition cc_empty : comb_circuit 0 0 := cc_out [].

Definition cc_false {I} : comb_circuit I 1 := cc_bool false (cc_out [Fin.R _ Fin.F1]).

Definition cc_if {I O} (s : comb_circuit I 1) (t f : comb_circuit I O) : comb_circuit I O.
Admitted.

Definition cc_pairO {I O1 O2} (cc1 : comb_circuit I O1) (cc2 : comb_circuit I O2)
  : comb_circuit I (O1 + O2).
Admitted.

Definition cc_let {I X O} (expr : comb_circuit I X) (body : comb_circuit (I + X) O)
  : comb_circuit I O.
Admitted.

Definition sc_empty : seq_circuit nil :=
  @mksc nil 0 cc_empty.

Definition sc_pair {mets1 mets2} (sc1 : seq_circuit mets1) (sc2 : seq_circuit mets2)
  : seq_circuit (mets1 ++ mets2).
Admitted.

(* COMPILE MODULE *)

Fixpoint anonymize (l : list (met_name_T * nat * nat + met_name_T * nat))
  : list (nat * nat + nat) :=
  match l with
  | nil => nil
  | cons (inl (_, sz, sz')) l' => cons (inl (sz, sz')) (anonymize l')
  | cons (inr (_, sz)) l' => cons (inr sz) (anonymize l')
  end.

Definition anonymize_all
  (M : list (mod_name_T * list (met_name_T * nat * nat + met_name_T * nat)))
  : list (nat * nat + nat) :=
  flat_map (fun ml => anonymize (snd ml)) M.

(* comb_circuit (1 + (1 + sz + 1 + 0) + sz) (sz + ((sz + 1) + 1))
   inputs:
   - 1 = enable read (ignored)
   - 1 + sz + 1 = enable write (ignored) + write value + commit write
   - sz = current value
   outputs:
   - sz = commit value
   - sz + 1 = read value + read abort (always false)
   - 1 = write abort (always false) *)
Definition cc_reg'writeval {sz} : comb_circuit (1 + (1 + sz + 1 + 0) + sz) sz :=
  cc_out (Vector.map (fun p => Fin.L _ (Fin.R _ (Fin.L _ (Fin.L _ (Fin.R _ p))))) (seq_all sz)).
Definition cc_reg'commit {sz} : comb_circuit (1 + (1 + sz + 1 + 0) + sz) 1 :=
  cc_out [Fin.L _ (Fin.R _ (Fin.L _ (Fin.R _ Fin.F1)))].
Definition cc_reg'currval {sz} : comb_circuit (1 + (1 + sz + 1 + 0) + sz) sz :=
  cc_out (Vector.map (Fin.R _) (seq_all sz)).
Definition cc_reg sz : comb_circuit (input (anonymize (interface_reg sz)) + sz)
                         (sz + output (anonymize (interface_reg sz))) :=
  cc_pairO (cc_if cc_reg'commit cc_reg'writeval cc_reg'currval)
    (cc_pairO (cc_pairO cc_reg'currval cc_false) cc_false).

(* comb_circuit (1 + (1 + sz + 1 + (1 + (1 + sz + 1 + 0))) + sz)
                (sz + ((sz + 1) + (1 + ((sz + 1) + 1))))
   inputs:
   - 1 = enable read0 (ignored)
   - 1 + sz + 1 = enable write0 (ignored) + write0 value + commit write0
   - 1 = enable read1 (ignored)
   - 1 + sz + 1 = enable write1 (ignored) + write1 value + commit write1
   - sz = current value
   outputs:
   - sz = commit value
   - sz + 1 = read0 value + read0 abort (always false)
   - 1 = write0 abort (always false)
   - sz + 1 = read1 value + read1 abort (always false)
   - 1 = write1 abort (always false) *)
Definition cc_ehr'write0val {sz}
  : comb_circuit (1 + (1 + sz + 1 + (1 + (1 + sz + 1 + 0))) + sz) sz :=
  cc_out (Vector.map (fun p => Fin.L _ (Fin.R _ (Fin.L _ (Fin.L _ (Fin.R _ p))))) (seq_all sz)).
Definition cc_ehr'commit0 {sz}
  : comb_circuit (1 + (1 + sz + 1 + (1 + (1 + sz + 1 + 0))) + sz) 1 :=
  cc_out [Fin.L _ (Fin.R _ (Fin.L _ (Fin.R _ Fin.F1)))].
Definition cc_ehr'write1valX {sz X}
  : comb_circuit (1 + (1 + sz + 1 + (1 + (1 + sz + 1 + 0))) + sz + X) sz :=
  cc_out
    (Vector.map
       (fun p => Fin.L _ (Fin.L _ (Fin.R _ (Fin.R _ (Fin.R _ (Fin.L _ (Fin.L _ (Fin.R _ p))))))))
       (seq_all sz)).
Definition cc_ehr'commit1X {sz X}
  : comb_circuit (1 + (1 + sz + 1 + (1 + (1 + sz + 1 + 0))) + sz + X) 1 :=
  cc_out [Fin.L _ (Fin.L _ (Fin.R _ (Fin.R _ (Fin.R _ (Fin.L _ (Fin.R _ Fin.F1))))))].
Definition cc_ehr'currval {sz}
  : comb_circuit (1 + (1 + sz + 1 + (1 + (1 + sz + 1 + 0))) + sz) sz :=
  cc_out (Vector.map (Fin.R _) (seq_all sz)).
Definition cc_ehr'currvalX {sz X}
  : comb_circuit (1 + (1 + sz + 1 + (1 + (1 + sz + 1 + 0))) + sz + X) sz :=
  cc_out (Vector.map (fun p => Fin.L _ (Fin.R _ p)) (seq_all sz)).
Definition cc_ehr sz : comb_circuit (input (anonymize (interface_ehr sz)) + sz)
                         (sz + output (anonymize (interface_ehr sz))) :=
  cc_let (cc_if cc_ehr'commit0 cc_ehr'write0val cc_ehr'currval)
    (cc_pairO
       (cc_if cc_ehr'commit1X cc_ehr'write1valX (cc_out (Vector.map (Fin.R _) (seq_all sz))))
       (cc_pairO (cc_pairO cc_ehr'currvalX cc_false)
          (cc_pairO cc_false
             (cc_pairO (cc_pairO (cc_out (Vector.map (Fin.R _) (seq_all sz))) cc_false)
                cc_false)))).

Definition cc_top' {M} (schedule : list (value_method M + rule M + action_method M))
  : comb_circuit (input (anonymize (interface_top schedule)) + output (anonymize_all M))
      (input (anonymize_all M) + output (anonymize (interface_top schedule))).
Admitted.
Definition cc_top {M} (subs : seq_circuit (anonymize_all M))
  (schedule : list (value_method M + rule M + action_method M))
  : comb_circuit (input (anonymize (interface_top schedule)) + regs_sc subs)
      (regs_sc subs + output (anonymize (interface_top schedule))).
Admitted.

Fixpoint compile' M (subs : seq_circuit (anonymize_all M)) {l} (m' : module' M l)
  : seq_circuit (anonymize l) :=
  match m' in module' M l return seq_circuit (anonymize_all M) -> seq_circuit (anonymize l) with
  | mod_reg sz => fun _ => mksc sz (cc_reg sz)
  | mod_ehr sz => fun _ => mksc sz (cc_ehr sz)
  | mod_top schedule => fun subs => mksc (regs_sc subs) (cc_top subs schedule)
  | mod_sub m sub m' =>
      fun subs => compile' (cons (m, _) _) (sc_pair (compile' nil sc_empty sub) subs) m'
  end subs.
Definition compile {l} (m : module l) : seq_circuit (anonymize l) :=
  compile' nil sc_empty m.





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



(* DOING:
   - mechanism preventing value method calls from violating ORAAT semantics
       (currently value method calls do not consider previously completed actions)
   - mechanism preventing aborting action method calls from violating ORAAT semantics
       (currently we do calculate when an action aborts, but we have yet to use that to
        appropariately abort an entire rule or action method)
   - allow for arbitrary interleaving of value methods, rules, and action methods
       (currently they are always scheduled in the order listed above)
   - special compilation for value methods with no arguments
   - primitive modules for registers, phemeral history registers
*)



(* COMBINATIONAL CIRCUIT *)

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

(* TODOC *)
Fixpoint cc_build {n I} (f : Fin.t n -> comb_circuit I 1) : comb_circuit I n :=
  match n as n return (Fin.t n -> comb_circuit I 1) -> comb_circuit I n with
  | 0 => fun _ => cc_out []
  | S n' => fun f => cc_pair (f Fin.F1) (cc_build (fun p => f (Fin.FS p)))
  end f.

(* VALUE *)



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
                               (cc_build (fun r => cc_or
                                                     (FinL (FinR (FinL (FinL (FinL r)))))
                                                     (FinR (FinR (FinL (FinL (FinL r)))))
                                                     (cc_out [FinR Fin1])))
                               (cc_build (fun r => cc_mux
                                                     (FinL (FinR (FinL (FinL (FinL r)))))
                                                     (FinL (FinR (FinL (FinL (FinR r)))))
                                                     (FinR (FinR (FinL (FinL (FinR r)))))
                                                     (cc_out [FinR Fin1]))))
                            (cc_build (fun r => cc_and
                                                  (FinL (FinR (FinL (FinL (FinL r)))))
                                                  (FinR (FinR (FinL (FinL (FinL r)))))
                                                  (cc_or
                                                     (FinL (FinL (FinR (FinL (FinR r)))))
                                                     (FinL (FinR (FinR (FinL (FinR r)))))
                                                     (cc_or (FinL (FinR Fin1)) (FinR Fin1)
                                                        (cc_out [FinR Fin1]))))))
                         (cc_pair (* AAA *)
                            (cc_pair
                               (cc_build (fun a => cc_or
                                                     (FinL (FinR (FinR (FinL (FinL a)))))
                                                     (FinR (FinR (FinR (FinL (FinL a)))))
                                                     (cc_out [FinR Fin1])))
                               (cc_build (fun a => cc_mux
                                                     (FinL (FinR (FinR (FinL (FinL a)))))
                                                     (FinL (FinR (FinR (FinL (FinR a)))))
                                                     (FinR (FinR (FinR (FinL (FinR a)))))
                                                     (cc_out [FinR Fin1]))))
                            (cc_build (fun a => cc_and
                                                  (FinL (FinR (FinR (FinL (FinL a)))))
                                                  (FinR (FinR (FinR (FinL (FinL a)))))
                                                  (cc_or
                                                     (FinL (FinL (FinR (FinR (FinR a)))))
                                                     (FinL (FinR (FinR (FinR (FinR a)))))
                                                     (cc_or (FinL (FinR Fin1)) (FinR Fin1)
                                                        (cc_out [FinR Fin1]))))))))
  | a_if c t f => cc_connect (* N = 2 + ((1 + (RRR + AAA)) + (1 + (RRR + AAA))) *)
                    (cc_pair
                       (cc_map FinL (compile_value c))
                       (cc_pair (compile_action t) (compile_action f)))
                    (cc_pair
                       (cc_mux (FinL Fin1) (FinR (FinL (FinL Fin1))) (FinR (FinR (FinL Fin1)))
                          (cc_or (FinL (FinL Fin2)) (FinR Fin1) (cc_out [FinR Fin1])))
                       (cc_not (FinL Fin1)
                          (cc_pair (* RRR + AAA *)
                             (cc_pair (* RRR *)
                                (cc_pair
                                   (cc_build
                                      (fun r =>
                                         cc_and
                                           (FinL (FinL Fin1))
                                           (FinL (FinR (FinL (FinR (FinL (FinL (FinL r)))))))
                                           (cc_and
                                              (FinL (FinR Fin1))
                                              (FinL (FinL (FinR (FinR (FinR (FinL (FinL (FinL r))))))))
                                              (cc_or (FinL (FinR Fin1)) (FinR Fin1)
                                                 (cc_out [FinR Fin1])))))
                                   (cc_build
                                      (fun r =>
                                         cc_mux
                                           (FinL (FinL Fin1))
                                           (FinL (FinR (FinL (FinR (FinL (FinL (FinR r)))))))
                                           (FinL (FinR (FinR (FinR (FinL (FinL (FinR r)))))))
                                           (cc_out [FinR Fin1]))))
                                (cc_build
                                   (fun r =>
                                      cc_and
                                        (FinL (FinL Fin1))
                                        (FinL (FinR (FinL (FinR (FinL (FinR r))))))
                                        (cc_and
                                           (FinL (FinR Fin1))
                                           (FinL (FinL (FinR (FinR (FinR (FinL (FinR r)))))))
                                           (cc_or (FinL (FinR Fin1)) (FinR Fin1)
                                              (cc_out [FinR Fin1]))))))
                             (cc_pair (* AAA *)
                                (cc_pair
                                   (cc_build
                                      (fun a =>
                                         cc_and
                                           (FinL (FinL Fin1))
                                           (FinL (FinR (FinL (FinR (FinR (FinL (FinL a)))))))
                                           (cc_and
                                              (FinL (FinR Fin1))
                                              (FinL (FinL (FinR (FinR (FinR (FinR (FinL (FinL a))))))))
                                              (cc_or (FinL (FinR Fin1)) (FinR Fin1)
                                                 (cc_out [FinR Fin1])))))
                                   (cc_build
                                      (fun a =>
                                         cc_mux
                                           (FinL (FinL Fin1))
                                           (FinL (FinR (FinL (FinR (FinR (FinL (FinR a)))))))
                                           (FinL (FinR (FinR (FinR (FinR (FinL (FinR a)))))))
                                           (cc_out [FinR Fin1]))))
                                (cc_build
                                   (fun a =>
                                      cc_and
                                        (FinL (FinL Fin1))
                                        (FinL (FinR (FinL (FinR (FinR (FinR a))))))
                                        (cc_and
                                           (FinL (FinR Fin1))
                                           (FinL (FinL (FinR (FinR (FinR (FinR (FinR a)))))))
                                           (cc_or (FinL (FinR Fin1)) (FinR Fin1)
                                              (cc_out [FinR Fin1])))))))))
  | a_write i arg => cc_let (* I + O = (lengthsig + RR + VV + AA) + 2 *)
                       (cc_map FinL (compile_value arg))
                       (cc_pair
                          (cc_out [FinR Fin2])
                          (cc_pair (* RRR + AAA *)
                             (cc_pair (* RRR *)
                                (cc_pair
                                   (cc_bool true (cc_bool false
                                                    (cc_out (build (fun r =>
                                                                      if Fin.eqb r (getFin i)
                                                                      then FinL (FinR Fin1)
                                                                      else FinR Fin1)))))
                                   (cc_bool false (cc_out (build (fun r =>
                                                                    if Fin.eqb r (getFin i)
                                                                    then FinL (FinR Fin1)
                                                                    else FinR Fin1)))))
                                (cc_bool false
                                   (cc_out
                                      (build (fun r =>
                                                if Fin.eqb r (getFin i)
                                                then FinL (FinL (FinL (FinL (FinR (FinR r)))))
                                                else FinR Fin1)))))
                             (cc_bool false (cc_out (rep (FinR Fin1)))))) (* AAA *)
  | a_call i arg => cc_let (* I + O = (lengthsig + RR + VV + AA) + 2 *)
                      (cc_map FinL (compile_value arg))
                      (cc_pair
                         (cc_out [FinR Fin2])
                         (cc_pair (* RRR + AAA *)
                            (cc_bool false (cc_out (rep (FinR Fin1)))) (* RRR *)
                            (cc_pair (* AAA *)
                               (cc_pair
                                  (cc_bool true (cc_bool false
                                                   (cc_out (build (fun a =>
                                                                     if Fin.eqb a (getFin i)
                                                                     then FinL (FinR Fin1)
                                                                     else FinR Fin1)))))
                                  (cc_bool false (cc_out (build (fun a =>
                                                                   if Fin.eqb a (getFin i)
                                                                   then FinL (FinR Fin1)
                                                                   else FinR Fin1)))))
                               (cc_bool false
                                  (cc_out
                                     (build (fun a =>
                                               if Fin.eqb a (getFin i)
                                               then FinL (FinL (FinR (FinL a)))
                                               else FinR Fin1)))))))
  | a_abort => cc_bool true (cc_bool false (cc_out (FinL (FinR Fin1) :: rep (FinR Fin1))))
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
    args_am : var_T;
    body_am : action args_am R V A;
    }.
Arguments name_am {R V A}.
Arguments args_am {R V A}.
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

Fixpoint l_of_L R M (L : list (value_method R M + rule R M + action_method R M))
  : list (vm_name_T + am_name_T) :=
  match L with
  | nil => nil
  | inl (inl vm) :: L' => inl (name_vm vm) :: (l_of_L L')
  | inl (inr _) :: L' => l_of_L L'
  | inr am :: L' => inr (name_am am) :: (l_of_L L')
  end.

(* a language module using children M *)
Inductive module' M : list (vm_name_T + am_name_T) -> Type :=
| mk_mod (R : list reg_T) (L : list (value_method R M + rule R M + action_method R M))
  : module' M (l_of_L L)
| child_mod {l l'} (m : mod_name_T) (child : module' [] l) (m' : module' ((m, l) :: M) l')
  : module' M l'.
Arguments mk_mod {M}.
Arguments child_mod {M l l'}.
Definition module := module' [].

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

