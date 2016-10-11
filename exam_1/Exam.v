Require Export SfLib.

(* ********************************************** *)
(* Problem 1 *)
(* ********************************************** *)

Inductive member {X} : X -> list X -> Prop :=
 | member_here : forall x xs,
    member x (x::xs)
 | member_later: forall x y xs,
    member x xs ->
    member x (y::xs).

Theorem app_member_left: forall (X:Type) (x:X) (xs ys : list X),
  member x xs -> member x (xs++ys).
Proof.
  intros.
  induction H.
  - apply member_here.
  - simpl. apply member_later... assumption.
Qed.

Theorem app_member_right: forall (X:Type) (x:X) (xs ys : list X),
  member x ys -> member x (xs++ys).
Proof.
  intros. 
  induction xs. 
  - simpl.  assumption.
  - simpl.  apply member_later.  assumption.
Qed.
 
Theorem or_app_member: forall (X:Type) (x:X) (xs ys : list X),
  member x xs \/ member x ys -> member x (xs++ys).
Proof.
  intros. 
  destruct H.
  apply app_member_left. assumption.
  apply app_member_right. assumption.
Qed.

Theorem app_or_member: forall (X:Type) (x:X) (xs ys : list X),
  member x (xs++ys) -> member x xs \/ member x ys.
Proof.
  intros.
  induction xs .
  right. simpl in H. assumption.
  simpl. inversion H.
  - left. apply member_here.
  - apply IHxs in H2. destruct H2.
   + left. apply member_later. assumption.
   + right. assumption.
Qed.


(* ********************************************** *)
(* Problem 2 *)
(* ********************************************** *)

(* States *)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

(* Arithmetic and boolean expressions *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

(* Commands *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'REPEAT' c 'UNTIL' b 'END'" := 
   (CRepeat c b) (at level 80, right associativity).

(* Evaluation relation *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || (update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''
  | E_RepeatEnd: forall b c st st',
      c / st || st' ->
      beval st' b = true ->
      (REPEAT c UNTIL b END) / st || st'
  | E_RepeatLoop: forall b c st st' st'',
      c / st || st' ->
      beval st' b = false ->
      (REPEAT c UNTIL b END) / st' || st'' ->
      (REPEAT c UNTIL b END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" 
  | Case_aux c "E_RepeatEnd" | Case_aux c "E_RepeatLoop" ].

(* Assertions *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* Hoare triples *)

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(* Assertions *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(* Assignment *)

(*
             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}
*)


Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(* Consequence *)

(*
                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

(* Skip *)

(*
             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* Sequencing *)

(*
               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(* Conditional *)

(*
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 
*)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(* While *)

(*
               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}
    The proposition [P] is called an _invariant_ of the loop.
*)

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on [He], because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just [c]. *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  ceval_cases (induction He) Case;
    try (inversion Heqwcom); subst; clear Heqwcom.
  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false. assumption.
  Case "E_WhileLoop".
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(* Repeat *)

Lemma hoare_repeat: forall P Q c b,
  {{P}} c {{Q}} ->
  (fun st => Q st /\ ~ (bassn b st)) ->> P -> 
  {{P}} REPEAT c UNTIL b END {{fun st => Q st /\ (bassn b st)}}.
Proof. 
  intros P Q c b Hhoare. intros Q'. intros st st'.
  intros He HP.
  remember (REPEAT c UNTIL b END) as wcom eqn:Heqwcom.
  ceval_cases (induction He) Case;
    try (inversion Heqwcom); subst; clear Heqwcom.
  (*repeat end*)
    - split.
      + apply (Hhoare st st'). assumption.  assumption.
      + assumption.
(* repeat loop *)
    - apply IHHe2. reflexivity. apply Q'. split.
      apply (Hhoare st st'). assumption. assumption. 
      apply bexp_eval_false. assumption.
Qed.
  
     
  

(* ********************************************** *)
(* Problem 3 *)
(* ********************************************** *)

(* Types *)

Inductive ty : Type := 
  | TBool  : ty 
  | TArrow : ty -> ty -> ty
  | Tree : ty -> ty.

(* Terms *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tbranch : tm -> tm -> tm -> tm
  | tleaf : tm
  | tcase : tm -> tm -> id -> id -> id -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "ttrue" 
  | Case_aux c "tfalse" | Case_aux c "tif" 
  | Case_aux c "tbranch" | Case_aux c "tleaf"
  | Case_aux c "tcase"].

(* Values *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse
  | v_leaf : 
      value tleaf
  | v_branch : forall t1 t2 t3,
     value t1 -> value t2 -> value t3 ->
     value (tbranch t1 t2 t3).

Hint Constructors value.

(* Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | tleaf => tleaf
  | tbranch t1 t2 t3 =>
      tbranch ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | tcase t1 t2 xt y zt t3 =>
      tcase ([x:=s] t1) t2 xt y zt 
    ( if (eq_id_dec x xt) then t3 else
      if (eq_id_dec x y) then t3 else
      if (eq_id_dec x zt) then t3 else
      ([x:=s] t3)
     )
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* Evaluation relation *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_BranchLeft : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tbranch t1 t2 t3) ==> (tbranch t1' t2 t3)
| ST_BranchMiddle : forall t1  t2 t2' t3,
      value t1 ->
      t2 ==> t2' ->
      (tbranch t1 t2 t3) ==> (tbranch t1 t2' t3)
| ST_BranchRight : forall t1 t2 t3 t3',
      value t1 ->
      value t2 ->
      t3 ==> t3' ->
      (tbranch t1 t2 t3) ==> (tbranch t1 t2 t3')
| ST_TCase: forall t1 t1' t2 xt y zt t3,
   t1 ==> t1' ->
   (tcase t1 t2 xt y zt t3) ==> (tcase t1' t2 xt y zt t3)
| ST_TCaseLeaf: forall t2 xt y zt t3,
    (tcase tleaf t2 xt y zt t3) ==> t2
| ST_TCaseBranch : forall v1 v2 v3 t2 xt y zt t3,
    value (tbranch v1 v2 v3) -> 
    (tcase (tbranch v1 v2 v3) t2 xt y zt t3) ==>
     [xt:=v1]([y:=v2]([zt:=v3]t3))

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue" 
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" 
  | Case_aux c "ST_TBranchLeft" | Case_aux c "ST_TBranchMiddle"
  | Case_aux c "ST_TBranchRight" | Case_aux c "ST_TCase"
  | Case_aux c "ST_TCaseLeaf" | Case_aux c "ST_TCaseBranch"].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(* Contexts *)

Module PartialMap.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

(** Informally, we'll write [Gamma, x:T] for "extend the partial
    function [Gamma] to also map [x] to [T]."  
Formally, we use the
    function [extend] to add a binding to a partial map. *)

Definition extend {A:Type} 
(Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->                       
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto.
Qed.

End PartialMap.

Definition context := partial_map ty.

(* Typing relation *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T
   | T_Leaf : forall T Gamma,
      Gamma |- tleaf \in Tree T
   | T_Branch : forall T Gamma t1 t2 t3,
      Gamma |- t1 \in Tree T ->
      Gamma |- t2 \in  T ->
      Gamma |- t3 \in Tree T ->
      Gamma |- (tbranch t1 t2 t3) \in Tree T
    | T_TCase : forall Gamma xt T y zt t2 T' t0 t1,
     extend (extend (extend Gamma xt (Tree T)) y T ) zt (Tree T) 
        |- t2 \in T' ->
    Gamma |- t0 \in Tree T ->
    Gamma |- t1 \in T' ->
    Gamma |-  (tcase t0 t1 xt y zt t2) \in T'

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_True" 
  | Case_aux c "T_False" | Case_aux c "T_If" 
  | Case_aux c "T_Leaf" | Case_aux c "T_Branch" 
  | Case_aux c "T_TCase" ].

Hint Constructors has_type.

(* Canonical Forms *)

Lemma cannonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma cannonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x. exists t0.  auto.
Qed.

Lemma cannonical_forms_tree: forall t T,
   empty |- t \in Tree T->
   value t ->
   t = tleaf \/ 
   exists t1 t2 t3, t = tbranch t1 t2 t3.
Proof.
   intros.
   inversion H0; intros; subst; try inversion H; subst; auto.
   right... exists t1. exists t2. exists t3. reflexivity.
Qed.
   
(* Progress, by induction on type derivation *)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    (* contradictory: variables cannot be typed in an 
       empty context *)
    inversion H. 

  Case "T_App". 
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a 
       value or steps... *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is also a value".
        assert (exists x0 t0, t1 = tabs x0 T11 t0).
        eapply cannonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...

      SSCase "t2 steps".
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...

    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  Case "T_If".
    right. destruct IHHt1...
    
    SCase "t1 is a value".
      destruct (cannonical_forms_bool t1); subst; eauto.

    SCase "t1 also steps".
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...
  Case "T_Branch".
     destruct IHHt1...
     destruct IHHt2...
     destruct IHHt3...
     destruct H1; right...
     destruct H0; right...
     destruct H; right...
  Case "T_TCase".      
     apply cannonical_forms_tree in Ht2.
     destruct Ht2.
     rewrite H.
     right.
     exists t1...
     destruct H. destruct H. destruct H.
     rewrite H.
     right...
     subst.
     destruct IHHt2...
     destruct H. exists (tcase x2 t1 xt y zt t2)...
Qed.


