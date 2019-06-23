(*
  Author: Cenobio Moisés Vázquez Reyes
*)

Require Import Coq.Strings.String.
Require Import List.
Require Import Bool.
Require Import Arith.
Require Import Coq.Logic.FunctionalExtensionality.


Definition State := nat.
Definition At := string.


Inductive PathF : Type :=
  | Var     : At -> PathF
  | Neg     : At -> PathF
  | ConjP   : PathF -> PathF -> PathF
  | DisyP   : PathF -> PathF -> PathF
  | Until   : PathF -> PathF -> PathF
  | Release : PathF -> PathF -> PathF
  | X       : PathF -> PathF.

Infix "∧" := ConjP (at level 20).
Infix "∨" := DisyP (at level 20).
Infix "U" := Until (at level 20).
Infix "V" := Release (at level 20).

Fixpoint negP (ф:PathF) : PathF :=
  match ф with
  | Var a => Neg a
  | Neg a => Var a
  | ф₁ ∧ ф₂ => (negP ф₁) ∨ (negP ф₂)
  | ф₁ ∨ ф₂ => (negP ф₁) ∧ (negP ф₂)
  | ф₁ U ф₂ => (negP ф₁) V (negP ф₂)
  | ф₁ V ф₂ => (negP ф₁) U (negP ф₂)
  | X ф' => X (negP ф')
  end.


Definition bot := Var EmptyString.
Definition top := Neg EmptyString.


Definition impP (ф₁ ф₂:PathF) : PathF := DisyP (negP ф₁) ф₂.

Definition F ф := top U ф.
Definition G ф := bot V ф.

Definition Path := State -> (At -> bool).

Definition path_sub (π:Path) (i:State) := π i.
Definition path_up (π:Path) (j:State) := fun (s:State) => π (s+j).

Axiom state_bot : forall π s, (path_sub π s) EmptyString = false.
Axiom state_top : forall π s, (path_sub π s) EmptyString = true -> False.

Fixpoint semanticLTL (π:Path) (ф:PathF) :=
  match ф with
  | Var a => (path_sub π 0) a = true
  | Neg a => (path_sub π 0) a = false
  | ф₁ ∧ ф₂ => (semanticLTL π ф₁) /\ (semanticLTL π ф₂)
  | ф₁ ∨ ф₂ => (semanticLTL π ф₁) \/ (semanticLTL π ф₂)
  | ф₁ U ф₂ => exists i, (semanticLTL (path_up π i) ф₂) /\
                       (forall j, j<i -> semanticLTL (path_up π j) ф₁)
  | ф₁ V ф₂ => (forall i, semanticLTL (path_up π i) ф₂) \/
             (exists i, (semanticLTL (path_up π i) ф₁) /\
             (forall j, j<=i -> semanticLTL (path_up π j) ф₂))
  | X ф' => semanticLTL (path_up π 1) ф'
  end.

Infix "⊨" := semanticLTL (at level 40).


Lemma n_eq_neq : forall n m:nat, n=m \/ n<>m.
Proof.
assert (forall n m : nat, {n = m} + {n <> m}).
  apply Nat.eq_dec.
intros.
destruct (H n m).
left; trivial.
right; trivial.
Qed.


Proposition negP_forms : forall ф π, π ⊨ ф -> ~ π ⊨ negP ф.
Proof.
induction ф.
(* a *)
intros.
simpl.
rewrite H.
intuition.
(* ¬a *)
intros; simpl; rewrite H;
intuition.
(* ф₁ ∧ ф₂ *)
intros.
simpl; intuition.
apply IHф1 in H1; trivial; apply H.
apply IHф2 in H1; trivial; apply H.
(* ф₁ ∨ ф₂ *)
intros.
simpl; intuition; destruct H.
apply IHф1 in H; trivial.
apply IHф2 in H; trivial.
(* ф₁ U ф₂ *)
simpl; intuition.
destruct H; destruct H.
apply IHф2 in H; trivial.
destruct H; destruct H1.
destruct H; destruct H0.
assert (x=x0 \/ x<>x0).
  apply n_eq_neq.
destruct H3.
rewrite H3 in H.
assert (path_up π x0 ⊨ negP ф2).
  apply H2; intuition.
apply IHф2 in H; trivial.
apply not_eq in H3.
destruct H3.
assert (path_up π x ⊨ negP ф2).
  apply H2; intuition.
apply IHф2 in H; trivial.
assert (path_up π x0 ⊨ ф1).
  apply H1; trivial.
apply IHф1 in H4; trivial.
(* ф₁ R ф₂ *)
simpl; intuition.
destruct H0; destruct H.
assert (path_up π x ⊨ ф2).
  apply H1.
apply IHф2 in H2; trivial.
destruct H0; destruct H.
destruct H1; destruct H1.
assert (x=x0 \/ x<>x0).
  apply n_eq_neq.
destruct H3.
rewrite H3 in H.
assert (path_up π x0 ⊨ ф2).
  apply H2; intuition.
apply IHф2 in H4; trivial.
apply not_eq in H3.
destruct H3.
assert (path_up π x ⊨ ф2).
  apply H2; intuition.
apply IHф2 in H4; trivial.
assert (path_up π x0 ⊨ negP ф1).
  apply H0; intuition.
apply IHф1 in H1; trivial.
(* Xф' *)
simpl; intuition.
apply IHф in H; trivial.
Qed.


Lemma distr_X_DisyP : forall π ф₁  ф₂, π ⊨ X (ф₁ ∨ ф₂) <-> π ⊨ X ф₁ ∨ X ф₂.
Proof.
split.
intros; trivial.
intros; trivial.
Qed.


Lemma distr_X_ConjP : forall π ф₁  ф₂, π ⊨ X (ф₁ ∧ ф₂) <-> π ⊨ X ф₁ ∧ X ф₂.
Proof.
split.
intros; trivial.
intros; trivial.
Qed.

Lemma path_comn_i_j : forall π i j,
                         (path_up (path_up π i) j) = (path_up (path_up π j) i).
Proof.
intros.
unfold path_up.
apply functional_extensionality.
intros.
rewrite plus_assoc_reverse.
rewrite plus_assoc_reverse.
pattern (j+i); rewrite Nat.add_comm; trivial.
Qed.


Lemma distr_X_U : forall π ф₁  ф₂, π ⊨ X (ф₁ U ф₂) <-> π ⊨ X ф₁ U X ф₂.
Proof.
split.
(* -> *)
simpl; intros.
destruct H.
exists x.
split.
destruct H.
rewrite path_comn_i_j; trivial.
destruct H.
intros; rewrite path_comn_i_j.
apply H0; trivial.
(* <- *)
simpl; intros.
destruct H.
exists x.
split.
destruct H.
rewrite path_comn_i_j; trivial.
intros; rewrite path_comn_i_j.
apply H; trivial.
Qed.


Lemma distr_F_DisyP : forall π ф₁  ф₂, π ⊨ F (ф₁ ∨ ф₂) <-> π ⊨ F ф₁ ∨ F ф₂.
Proof.
split.
(* -> *)
simpl; intros.
destruct H; destruct H.
destruct H.
left.
exists x; split; trivial.
right.
exists x; split; trivial.
(* <- *)
simpl; intros.
destruct H; destruct H; destruct H.
exists x.
split.
left; trivial.
trivial.
exists x.
split.
right; trivial.
trivial.
Qed.


Lemma min_n_m : forall n m, (min n m = n) \/ (min n m = m).
Proof.
assert (forall n m : nat, {Nat.min n m = n} + {Nat.min n m = m}).
  apply Nat.min_dec.
intros.
destruct (H n m).
left; trivial.
right; trivial.
Qed.


Lemma distr_G_ConjP : forall π ф₁  ф₂, π ⊨ G (ф₁ ∧ ф₂) <-> π ⊨ G ф₁ ∧ G ф₂.
Proof.
split.
(* -> *)
simpl; intros.
split.
destruct H.
left.
intros; apply H.
right.
destruct H; destruct H.
exists x.
split.
trivial.
intros; apply H0; trivial.
destruct H.
left.
intros; apply H.
destruct H; destruct H.
right.
exists x.
split.
trivial.
intros.
assert (path_up π x ⊨ ф₂).
  apply H0; trivial.
apply H0; trivial.
(* <- *)
simpl; intros.
destruct H.
destruct H; destruct H0.
left.
intros.
split.
apply H.
apply H0.
right.
destruct H0.
exists x.
split.
apply H0.
intros.
split.
destruct H0.
apply H.
destruct H0.
apply H2; trivial.
right.
destruct H; destruct H.
exists x.
split.
trivial.
intros.
split.
apply H1; trivial.
apply H0.
destruct H; destruct H.
destruct H0; destruct H0.
right.
exists (min x x0).
split.
assert (min x x0 = x \/ min x x0 = x0).
  apply min_n_m.
destruct H3.
rewrite <- H3 in H.
trivial.
rewrite <- H3 in H0.
trivial.
intros.
split.
assert (min x x0 = x \/ min x x0 = x0).
  apply min_n_m.
destruct H4.
rewrite <- H4 in H1.
apply H1; trivial.
apply H1.
apply Nat.min_glb_iff in H3.
apply H3.
apply H2.
apply Nat.min_glb_iff in H3.
apply H3.
Qed.

Lemma path_plus_i_j : forall π i j, path_up (path_up π i) j = path_up π (i+j).
Proof.
intros.
unfold path_up.
apply functional_extensionality.
intros.
pattern (i+j); rewrite Nat.add_comm.
rewrite plus_assoc_reverse; trivial.
Qed.


Lemma path_sub_j_0 : forall π j, path_sub (path_up π j) 0 = path_sub π j.
Proof.
intros.
unfold path_sub.
unfold path_up.
rewrite plus_O_n; trivial.
Qed.


Lemma path_up_0 : forall π, path_up π 0 = π.
Proof.
intros.
unfold path_up.
apply functional_extensionality.
intros.
rewrite Nat.add_0_r; trivial.
Qed.


Lemma idem_F : forall π ф, π ⊨ F (F ф) <-> π ⊨ F ф.
Proof.
split.
(* -> *)
intros.
simpl in *.
destruct H.
destruct H.
destruct H.
destruct H.
rewrite path_plus_i_j in H.
exists (x+x0).
split.
apply H.
intros.
apply state_bot.
(* <- *)
simpl; intuition.
destruct H; destruct H.
exists x.
split.
exists 0.
split.
rewrite path_plus_i_j.
rewrite Nat.add_0_r.
apply H.
intros.
contradict H1; apply Nat.nlt_0_r.
intros.
apply H0; trivial.
Qed.


Lemma idem_G : forall π ф, π ⊨ G (G ф) <-> π ⊨ G ф.
Proof.
split.
(* -> *)
intros.
simpl in *.
destruct H.
left.
intros.
destruct (H 0).
rewrite <- (plus_O_n i).
rewrite <- path_plus_i_j.
apply H0.
destruct H0.
destruct H0.
apply state_top in H0; contradiction.
right.
destruct H.
destruct H.
apply state_top in H; contradiction.
(* <- *)
intros.
simpl in *.
destruct H.
left.
left.
intros.
rewrite path_plus_i_j.
apply H.
right.
destruct H.
destruct H.
exists x.
split.
apply H.
apply state_top in H; intuition.
Qed.


Theorem FP_U : forall π ф₁ ф₂, π ⊨ ф₁ U ф₂ <-> π ⊨ ф₂ ∨ (ф₁  ∧ X (ф₁ U ф₂)).
Proof.
split.
(* -> *)
intros.
simpl in H.
destruct H.
destruct H.
destruct x.
rewrite path_up_0 in H.
left; trivial.
right.
split.
pattern π at 1; rewrite <- path_up_0.
apply H0.
apply Nat.lt_0_succ.
simpl.
exists x.
split.
rewrite path_plus_i_j.
apply H.
intros.
rewrite path_plus_i_j.
apply H0.
apply lt_n_S in H1; trivial.
(* <- *)
intros.
simpl in *.
destruct H.
exists 0.
split.
rewrite path_up_0; trivial.
intros.
contradict H0; apply Nat.nlt_0_r.
destruct H.
destruct H0.
destruct H0.
rewrite path_plus_i_j in H0.
exists (1 + x).
split.
apply H0.
intros.
destruct j.
rewrite path_up_0; trivial.
assert (S j = j+1).
  ring.
rewrite H3.
rewrite Nat.add_comm.
rewrite <- path_plus_i_j.
apply H1.
apply lt_S_n; trivial.
Qed.


Lemma distr_or_and : forall π ф₁ ф₂ ф₃,
                                    π ⊨ ф₁ ∨ (ф₂ ∧ ф₃) <-> π ⊨ (ф₁ ∨ ф₂) ∧ (ф₁ ∨ ф₃).
Proof.
split.
(* -> *)
intros.
split.
destruct H.
left; trivial.
right; apply H.
destruct H.
left; trivial.
right; apply H.
(* <- *)
intros.
destruct H.
destruct H.
left; trivial.
destruct H0.
left; trivial.
right; split.
apply H.
apply H0.
Qed.

Corollary FP_U_or : forall π ф₁  ф₂, π ⊨ ф₁ U ф₂ <-> π ⊨ (ф₂ ∨ ф₁) ∧ (ф₂ ∨ X (ф₁ U ф₂)).
Proof.
intros.
assert (π ⊨ ф₂ ∨ (ф₁ ∧ X (ф₁ U ф₂)) <-> π ⊨ (ф₂ ∨ ф₁) ∧ (ф₂ ∨ X (ф₁ U ф₂))).
apply distr_or_and.
destruct H.
split.
intros.
apply FP_U in H1.
apply H in H1; trivial.
intros.
apply FP_U.
apply H0; trivial.
Qed.


Theorem FP_R : forall π ф₁  ф₂, π ⊨ ф₁ V ф₂ <-> π ⊨ ф₂ ∧ (ф₁  ∨ (X (ф₁ V ф₂))).
Proof.
split.
(* -> *)
intros.
simpl in *.
split.
destruct H.
pattern π at 1; rewrite <- path_up_0.
apply H.
destruct H.
destruct H.
pattern π at 1; rewrite <- path_up_0.
apply H0.
apply Peano.le_0_n.
destruct H.
right.
left.
intros.
rewrite path_plus_i_j.
apply H.
destruct H.
destruct H.
destruct x.
left.
rewrite path_up_0 in H; trivial.
right.
right.
exists x.
split.
rewrite path_plus_i_j.
apply H.
intros.
rewrite path_plus_i_j.
apply H0.
apply le_n_S in H1; trivial.
(* -> *)
intros.
destruct H.
simpl.
destruct H0.
right.
exists 0.
split.
rewrite path_up_0; trivial.
intros.
apply le_n_0_eq in H1.
rewrite <- H1.
rewrite path_up_0; trivial.
simpl in H0.
destruct H0.
left.
intros.
destruct i.
rewrite path_up_0; trivial.
assert (S i = i+1).
  ring.
rewrite H1.
rewrite Nat.add_comm.
rewrite <- path_plus_i_j.
apply H0.
right.
destruct H0.
destruct H0.
rewrite path_plus_i_j in H0.
exists (1+x).
split.
apply H0.
intros.
destruct j.
rewrite path_up_0; trivial.
assert (S j = j+1).
  ring.
rewrite H3.
rewrite Nat.add_comm.
rewrite <- path_plus_i_j.
apply H1.
apply le_S_n; trivial.
Qed.

