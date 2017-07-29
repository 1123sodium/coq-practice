(*このプログラムは実数の公理からHeine-Borelの定理を導くことを目的とする*)




(*bool値に関する定義*)

Definition Is_true (b:bool) :Prop :=
  match b with
  | true => True
  | false => False
  end.

Lemma diff_true_false : true <> false.
Proof.
  intro. assert (Is_true true <-> Is_true false). rewrite H.
  split. intro. auto. intro. auto. simpl in H0.
  elim H0; clear H0; intros. apply H0. auto.
Qed.




(*自然数に関する定義*)

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | 0 => true
  | S n' => match m with
            | 0 => false
            | S m' => ble_nat n' m'
            end
  end.

Fixpoint max_nat (n m : nat) : nat :=
  if ble_nat n m then m else n.

Lemma nat_ref : forall n :nat, ble_nat n n = true.
Proof.
  intro. induction n. simpl. auto. simpl. apply IHn.
Qed.

Lemma nat_trans : forall n m l : nat, ble_nat n m = true -> ble_nat m l = true -> ble_nat n l = true.
Proof.
  intro. induction n as [ | n' ]. intros. simpl. auto.
  intro. induction m as [ | m' ]. intros. simpl in H. assert (H1 := diff_true_false).
  elim H1. rewrite H. auto.
  intro. induction l as [ | l' ]. intros. simpl in H0. assert (H1 := diff_true_false).
  elim H1. rewrite H0. auto.
  simpl. intros. apply (IHn' m' l' H H0).
Qed.

Lemma nat_total_ord : forall n m : nat, ble_nat n m = true \/ ble_nat m n = true.
Proof.
  intro. induction n as [ | n' ]. intros. simpl. left. auto.
  intro. induction m as [ | m' ]. simpl. right. auto.
  simpl. apply (IHn' m').
Qed.




(*リストに関する定義*)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint In (X:Type) (l:list X) (x:X) :Prop :=
  match l with
  | nil _ => False
  | cons _ x' l' => (x = x') \/ (In X l' x)
  end.




(*古典論理のトートロジー*)

(*二重否定除去の仮定*)
(*Coqは直感主義論理なのでこの仮定が必要*)
Axiom neg_elim : forall A : Prop, ~~A -> A.


Theorem AornotA : forall A : Prop, A \/ ~A.
Proof.
  intro. apply (neg_elim (A \/ ~A)).
  intro. apply H. right. intro. apply H. left. assumption.
Qed.

Corollary notAorA : forall A : Prop, ~A \/ A.
Proof.
  intro. elim (AornotA A). intro. right. auto. left. auto.
Qed.

Lemma not_and_or : forall A B:Prop, ~(A /\ B) -> ~A \/ ~B.
Proof.
  intros. apply (neg_elim (~A \/ ~B)).
  intro. apply H0. left. intro. apply H0. right. intro. apply H. split. assumption. assumption.
Qed.

Lemma not_forall : forall X:Type, forall A:X -> Prop, ~(forall x:X, A x) -> exists x:X, ~A x.
Proof.
  intros. elim (AornotA (exists x:X, ~A x)). auto.
  intro. elim H. intro. elim (AornotA (A x)). auto.
  intro. elim H0. exists x. assumption.
Qed.

Lemma not_exists : forall X:Type, forall A:X -> Prop, ~(exists x:X, A x) -> forall x:X, ~A x.
Proof.
  intros. intro. apply H. exists x. auto.
Qed.

Lemma neg_intro : forall A : Prop, A -> ~~A.
Proof.
  intros. intro. apply (H0 H).
Qed.

Lemma not_exists2 : forall X:Type, forall A B:X -> Prop, ~ (exists a : X, A a /\ B a) -> forall a : X, A a -> ~ B a.
Proof.
  intros. intro. apply H. exists a. split. auto. auto.
Qed.

Lemma and_l : forall A B : Prop, A /\ B -> A.
Proof.
  intros; elim H; intros; auto.
Qed.

Lemma and_r : forall A B : Prop, A /\ B -> B.
Proof.
  intros; elim H; intros; auto.
Qed.

Lemma Hilbert : forall A B : Prop, A -> (A -> B) -> B.
Proof.
  intros. apply (H0 H).
Qed.

Lemma equal : forall X : Type, forall A : X, A = A.
Proof.
  intros. auto.
Qed.




(*実数の公理*)


(*実数Rの導入*)
Inductive R : Set :=
  | R0 : R
  | R1 : R
  | plus : R -> R -> R
  | opp : R -> R
  | mult : R -> R -> R
  | inv : R -> R.

Parameter ord : R -> R -> Prop.


(*演算の公理*)
Notation "x + y" := (plus x y) (at level 50, left associativity).
Notation "- x" := (opp x).
Notation "x - y" := (x + (- y)).
Notation "x * y" := (mult x y) (at level 40, left associativity).
Notation "/ x" := (inv x).
Notation "x / y" := (mult x (/ y)).

Axiom plus_comm : forall a b : R, a + b = b + a.
Axiom plus_assoc : forall a b c : R, a + b + c = a + (b + c).
Axiom plus_opp_r : forall a : R, a - a = R0.
Axiom plus_0_r : forall a : R, a + R0 = a.
Axiom mult_comm : forall a b : R, a * b = b * a.
Axiom mult_assoc : forall a b c : R, a * b * c = a * (b * c).
Axiom mult_inv_r : forall a : R, a <> R0 -> a / a = R1.
Axiom mult_1_r : forall a : R, a * R1 = a.
Axiom distrib_l : forall a b c : R, a * (b + c) = (a * b) + (a * c).
Axiom R1_neq_R0 : R0 <> R1.


(*順序の公理*)
Notation "x <= y" := (ord x y).
Notation "x < y" := ((ord x y) /\ (x <> y)).
Notation "x >= y" := (ord y x).
Notation "x > y" := ((ord y x) /\ (x <> y)).
Notation "x <= y <= z" := (x <= y /\ y <= z).
Notation "x <= y < z" := (x <= y /\ y < z).
Notation "x < y <= z" := (x < y /\ y <= z).
Notation "x < y < z" := (x < y /\ y < z).

Axiom ord_ref : forall a : R, a <= a.
Axiom ord_asym : forall a b : R, a <= b -> b <= a -> a = b.
Axiom ord_trans : forall a b c : R, a <= b -> b <= c -> a <= c.
Axiom total_ord : forall a b : R, a <= b \/ b <= a.
Axiom ord_plus : forall a b c : R, a <= b -> a + c <= b + c.
Axiom ord_mult : forall a b : R, a >= R0 -> b >= R0 -> a * b >= R0.


(*実数の部分集合の型は R -> Prop を用いる、すなわち特性関数で部分集合を表す*)

(*連続性の公理*)
Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.
Definition is_lower_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x >= m.
Definition bounded_above (E:R -> Prop) := exists m:R, is_upper_bound E m.
Definition bounded_below (E:R -> Prop) := exists m:R, is_lower_bound E m.
Definition bounded (E:R -> Prop) := bounded_above E /\ bounded_below E.
Definition is_sup (E:R -> Prop) (m:R) := (is_upper_bound E m) /\ (forall x:R, is_upper_bound E x -> m <= x).
Definition is_inf (E:R -> Prop) (m:R) := (is_lower_bound E m) /\ (forall x:R, is_lower_bound E x -> m >= x).

Axiom continuity_of_real_numbers :
  forall E:R -> Prop, bounded_above E -> (exists x:R, E x) -> (exists m:R, is_sup E m).


(*自然数から実数への包含写像*)
Fixpoint inc (n:nat) :R :=
  match n with
  | 0 => R0
  | S n' => (inc n') + R1
  end.




(*実数の諸性質*)

(*集合としての性質*)
Definition included (E:R -> Prop) (F:R -> Prop) := forall x:R, F x -> E x.
Definition eqset (E:R -> Prop) (F:R -> Prop) := included E F /\ included F E.

Lemma eqset_trans : forall E F G : R -> Prop, eqset E F -> eqset F G -> eqset E G.
Proof.
  unfold eqset. unfold included. intros. elim H; clear H; intros. elim H0; clear H0; intros.
  split. intros. apply (H x (H0 x H3)). intros. apply (H2 x (H1 x H3)).
Qed.

Lemma eqset_sym : forall E F : R -> Prop, eqset E F -> eqset F E.
Proof.
  unfold eqset. unfold included. intros. elim H; clear H; intros. split. auto. auto.
Qed.


(*演算の性質*)
Lemma plus_opp_l : forall a : R, - a + a = R0.
Proof.
  intros. rewrite (plus_comm (- a) a). rewrite (plus_opp_r a). auto.
Qed.

Lemma plus_0_l : forall a : R, R0 + a = a.
Proof.
  intros. rewrite (plus_comm R0 a). rewrite (plus_0_r a). auto.
Qed.

Lemma mult_inv_l : forall a : R, a <> R0 -> / a * a = R1.
Proof.
  intros. rewrite (mult_comm (/ a) a). rewrite (mult_inv_r a H). auto.
Qed.

Lemma mult_1_l : forall a : R, R1 * a = a.
Proof.
  intros. rewrite (mult_comm R1 a). rewrite (mult_1_r a). auto.
Qed.

Lemma mult_0_r : forall a:R, a * R0 = R0.
Proof.
  intro. assert (H := distrib_l a R0 R0). rewrite (plus_0_r R0) in H.
  assert (a * R0 - (a * R0) = a * R0 + a * R0 - (a * R0)). rewrite <- H. reflexivity.
  rewrite (plus_assoc (a * R0) (a * R0) (- (a * R0))) in H0. rewrite (plus_opp_r (a * R0)) in H0.
  rewrite (plus_0_r (a * R0)) in H0. auto.
Qed.

Lemma mult_0_l : forall a:R, R0 * a = R0.
Proof.
  intros. rewrite (mult_comm R0 a). rewrite (mult_0_r a). auto.
Qed.

Lemma distrib_r : forall a b c : R, (a + b) * c = (a * c) + (b * c).
Proof.
  intros; rewrite (mult_comm (a + b) c); rewrite (distrib_l c a b);
  rewrite (mult_comm c a); rewrite (mult_comm c b); auto.
Qed.

Lemma minus1 : forall a:R, - a = a * (-R1).
Proof.
  intro. assert (H := distrib_l a R1 (- R1)). rewrite -> (plus_opp_r R1) in H. rewrite -> (mult_0_r a) in H.
  rewrite (mult_1_r a) in H. rewrite <- (plus_opp_r a) in H.
  assert ((- a) + a + (- a) = (- a) + a + a * - R1).
  rewrite (plus_assoc (- a) a (- a)). rewrite (plus_assoc (- a) a (a * - R1)). rewrite H. auto.
  rewrite (plus_comm (- a) a) in H0. rewrite (plus_opp_r a) in H0. rewrite (plus_comm R0 (- a)) in H0.
  rewrite (plus_comm R0 (a * - R1)) in H0. rewrite (plus_0_r (- a)) in H0. rewrite (plus_0_r (a * - R1)) in H0.
  auto.
Qed.

Lemma minus2 : forall a b:R, (- a) * (- b) = a * b.
Proof.
  intros. rewrite (minus1 a). rewrite (minus1 b). rewrite (mult_assoc a (- R1) (b * - R1)). 
  rewrite <- (mult_assoc (- R1) b (- R1)). rewrite (mult_comm (- R1) b).
  rewrite (mult_assoc b (- R1) (- R1)). rewrite <- (mult_assoc a b (- R1 * - R1)).
  rewrite <- (minus1 (- R1)). assert (H := plus_opp_r (- R1)).
  assert (R1 - R1 - - R1 = R1). rewrite (plus_assoc R1 (- R1) (- - R1)). rewrite H. rewrite (plus_0_r R1). auto.
  rewrite (plus_opp_r R1) in H0. rewrite (plus_comm R0 (- - R1)) in H0. rewrite (plus_0_r (- - R1)) in H0.
  rewrite H0. rewrite (mult_1_r (a * b)). reflexivity.
Qed.

Lemma minus3 : forall a:R, - - a = a.
Proof.
  intro. rewrite (minus1 (- a)). rewrite (minus1 a). rewrite (mult_assoc a (- R1) (- R1)).
  rewrite (minus2 R1 R1). rewrite (mult_1_r R1). rewrite  (mult_1_r a). auto.
Qed.

Lemma minus4 : forall a b:R, - (a - b) = b - a.
Proof.
  intros. rewrite (minus1 (a - b)). rewrite (mult_comm (a - b) (- R1)). rewrite (distrib_l (- R1) a (- b)).
  rewrite (mult_comm (- R1) a). rewrite <- (minus1 a). rewrite (mult_comm (- R1) (- b)).
  rewrite <- (minus1 (- b)). rewrite (minus3 b). rewrite (plus_comm (- a) b). auto.
Qed.

Lemma minus5 : R0 = - R0.
Proof.
  assert (R0 + R0 = - R0 + R0). rewrite (plus_0_r _). rewrite (plus_opp_l _). auto.
  rewrite (plus_0_r _) in H. rewrite (plus_0_r _) in H. auto.
Qed.


(*順序の性質*)
Lemma ord1 : forall x y:R, x < y \/ x = y \/ x > y.
Proof.
  intros. elim (total_ord x y). intro. elim (AornotA (x = y)). 
  intro. right. left. auto.
  intro. left. split. auto. auto.
  intro. elim(AornotA (x = y)).
  intro. right. left. auto.
  intro. right. right. split. auto. auto.
Qed.

Lemma ord2 : forall x y:R, ~(x <= y) -> x > y.
Proof.
  intros. elim (total_ord x y). intro. elim H. auto.
  intro. split. auto. elim (notAorA (x = y)). auto. intro. elim H. rewrite H1. assert (H2 := ord_ref y). auto.
Qed.

Lemma ord3 : forall x y:R, ~(x < y) -> x >= y.
Proof.
  intros. elim (ord1 x y). intro. elim H. auto.
  intro H1; elim H1; clear H1. intro. rewrite H0. apply (ord_ref y).
  intro. elim H0. intros. auto.
Qed.

Lemma ord3' : forall x y:R, ~(x > y) -> x <= y.
Proof.
  intros. elim (ord1 x y). intro. elim H0. intros. auto.
  intro H1; elim H1; clear H1. intro. rewrite H0. apply (ord_ref y).
  intro. elim H. auto.
Qed.

Lemma ord4 : R0 < R1.
Proof.
  split. elim (total_ord R0 R1). auto. intro.
  assert (H1 := ord_plus R1 R0 (- R1) H).
  rewrite (plus_opp_r R1) in H1. rewrite (plus_comm R0 (- R1)) in H1. rewrite (plus_0_r (- R1)) in H1.
  assert (H2 := ord_mult (- R1) (- R1) H1 H1). rewrite (minus2 R1 R1) in H2. rewrite (mult_1_r R1) in H2. auto.
  apply R1_neq_R0.
Qed.

Lemma ord5 : forall n:nat, R0 <= inc n.
Proof.
  intro. induction n as [ | n' ]. simpl. apply (ord_ref R0).
  simpl. assert (H := ord_plus R0 (inc n') R1 IHn'). rewrite (plus_0_l R1) in H.
  assert (H1 := ord4). elim H1; clear H1; intros. assert (H2 := ord_trans R0 R1 (inc n' + R1) H0 H). auto.
Qed.

Lemma ord6 : forall a b:R, a < b -> - b < - a.
Proof.
  intros. elim H; clear H; intros. split. assert (H1 := ord_plus a b (- a - b) H).
  rewrite (plus_comm (- a) (- b)) in H1. rewrite <- (plus_assoc b (- b) (- a)) in H1.
  rewrite (plus_opp_r b) in H1. rewrite (plus_0_l (- a)) in H1.
  rewrite (plus_comm (- b) (- a)) in H1. rewrite <- (plus_assoc a (- a) (- b)) in H1.
  rewrite (plus_opp_r a) in H1. rewrite (plus_0_l (-b)) in H1. auto.
  intro. apply H0. rewrite <- (minus3 a). rewrite <- (minus3 b).
  rewrite H1. auto.
Qed.

Lemma ord7 : forall a b c d:R, a < b -> c <= d -> a + c < b + d.
Proof.
  intros a b c d H H0; elim H; clear H; intros; split.
  assert (H2 := ord_plus a b c H). assert (H3 := ord_plus c d b H0).
  rewrite (plus_comm d b) in H3; rewrite (plus_comm c b) in H3.
  apply (ord_trans _ _ _ H2 H3).
  intro. apply H1. assert (H3 := ord_plus _ _ a H0).
  rewrite (plus_comm c a) in H3; rewrite H2 in H3; assert (H4 := ord_plus _ _ (- d) H3);
  rewrite (plus_comm d a) in H4; rewrite (plus_assoc _ _ _) in H4; rewrite (plus_assoc _ _ _) in H4;
  rewrite (plus_opp_r d) in H4; rewrite (plus_0_r) in H4; rewrite (plus_0_r) in H4; 
  apply (ord_asym _ _ H H4).
Qed.

Lemma ord8 : forall a b c:R, a < b -> a + c < b + c.
Proof.
  intros. elim H; clear H; intros. split. apply (ord_plus a b c H). intro.
  elim H0. assert (a + c - c = b + c - c). rewrite H1. auto.
  rewrite (plus_assoc a c (- c)) in H2. rewrite (plus_assoc b c (- c)) in H2.
  rewrite (plus_opp_r c) in H2. rewrite (plus_0_r a) in H2. rewrite (plus_0_r b) in H2. auto.
Qed.

Lemma ord9 : forall a b c d:R, a <= b -> c <= d -> a + c <= b + d.
Proof.
  intros. assert (H1 := ord_plus _ _ c H). assert (H2 := ord_plus _ _ b H0). 
  rewrite (plus_comm d b) in H2. rewrite (plus_comm c b) in H2. apply (ord_trans _ _ _ H1 H2).
Qed.

Lemma ord10 : forall a eps:R, forall E:R -> Prop, is_sup E a -> eps > R0 -> exists b:R, E b /\ b > a - eps.
Proof.
  intros. apply (neg_elim (exists b : R, E b /\ b > a - eps)). intro.
  assert (is_upper_bound E (a - eps)). unfold is_upper_bound. intros.
  assert (H3 := not_exists2 R _ _ H1 x H2). simpl in H3. assert (H4 := ord3' _ _ H3). auto.
  unfold is_sup in H. elim H; clear H; intros H H'. assert (H3 := H' (a - eps) H2).
  assert (H4 := ord_plus _ _ (eps - a) H3). rewrite plus_assoc in H4. rewrite <- (plus_assoc (- eps) eps (- a)) in H4.
  rewrite plus_opp_l in H4. rewrite plus_0_l in H4. rewrite (plus_comm eps (- a)) in H4. 
  rewrite <- plus_assoc in H4. rewrite (plus_opp_r a) in H4. rewrite plus_0_l in H4. elim H0; clear H0; intros H5 H6.
  apply H6. apply (ord_asym _ _ H4 H5).
Qed.

Lemma ord11 : forall a b:R, a < b <-> b > a.
Proof.
  intros. split. intro. elim H; clear H; intros; split; auto; auto.
  intro. elim H; clear H; intros; split; auto; auto.
Qed.


Lemma ord5' : forall n:nat, R0 < inc (S n).
Proof.
  intros. simpl.
  assert (H1 := ord7 _ _ _ _ ord4 (ord5 n)). rewrite plus_0_r in H1.
  rewrite plus_comm. auto.
Qed.

Lemma ord5'' : forall n:nat, inc n = R0 -> n = 0.
Proof.
  intros. induction n. auto. assert (H0 := ord5' n). elim H0; clear H0; intros.
  elim H1. rewrite H. auto.
Qed.

Lemma inverse : forall a :R, R0 < a -> R0 < / a.
Proof.
  intros. elim H; intros. assert (a <> R0). intro. elim H1. auto. clear H1. apply (neg_elim (R0 < / a)). intro.
  assert (H3 := ord3 _ _ H1). assert (H4 := ord_plus _ _ (- / a) H3). rewrite plus_0_l in H4.
  rewrite plus_opp_r in H4. assert (H5 := ord_mult _ _ H0 H4). rewrite minus1 in H5.
  rewrite <- mult_assoc in H5. rewrite (mult_inv_r _ H2) in H5. rewrite mult_1_l in H5.
  assert (H6 := ord4). assert (H7 := ord_plus _ _ R1 H5). rewrite plus_opp_l in H7. rewrite plus_0_l in H7.
  elim H6; intros. apply H9. apply (ord_asym _ _ H8 H7).
Qed.

Lemma ord12 : forall a b c :R, c > R0 -> a < b -> a * c < b * c.
Proof.
  intros. assert (H1 := ord8 _ _ (- a) H0). rewrite plus_opp_r in H1. elim H; intros.
  elim H1; intros. assert (H6 := ord_mult _ _ H4 H2). rewrite distrib_r in H6.
  assert (H7 := ord_plus _ _ (a * c) H6). rewrite plus_assoc in H7. rewrite minus1 in H7.
  rewrite mult_assoc in H7. rewrite (mult_comm (- R1) _) in H7. rewrite <- mult_assoc in H7.
  rewrite <- minus1 in H7. rewrite (plus_opp_l (a * c)) in H7. rewrite plus_0_r in H7. rewrite plus_0_l in H7.
  split. auto. intro. assert (a * c / c = b * c / c). rewrite H8; auto. rewrite mult_assoc in H9.
  rewrite mult_assoc in H9. rewrite (mult_inv_r _ H3) in H9. rewrite mult_1_r in H9. rewrite mult_1_r in H9.
  elim H5. rewrite H9. rewrite plus_opp_r. auto.
Qed.

Lemma ord13 : forall a b c:R, a < b -> b < c -> a < c.
Proof.
  intros. elim H; intros; elim H0; intros. split. apply (ord_trans _ _ _ H1 H3).
  intro. rewrite <- H5 in H3. elim H2. apply (ord_asym _ _ H1 H3).
Qed.

Lemma ord14 : R1 / inc 2 < R1.
Proof.
  simpl. rewrite plus_0_l. assert(H := ord4). assert (H1 := ord8 _ _ R1 H). rewrite plus_0_l in H1.
  assert (H2 := ord13 _ _ _ H H1).
  assert (H3 := ord12 _ _ (/ (R1 + R1)) (and_l _ _ (ord11 R0 (/ (R1 + R1))) (inverse _ H2)) H1).
  rewrite (mult_inv_r _ (and_r _ _ ((and_l _ _ (ord11 R0 (R1 + R1))) H2))) in H3. auto.
Qed.

Lemma ord15 : forall n m : nat, n <> m -> ble_nat n m = true -> inc n < inc m.
Proof.
  intro. induction n as [| n']. intros. split. apply (ord5 m). intro. simpl in H1.
  assert (inc m = R0). rewrite H1. auto. elim H. assert (H3 := ord5'' m H2). rewrite H3. auto.
  simpl. intro. induction m as [| m']. intros. assert (true = false). rewrite H0. auto.
  assert (H2 := diff_true_false H1). elim H2.
  intros. simpl. assert ((inc n' < inc m') -> (inc n' + R1 < inc m' + R1)).
  intros. apply (ord8 _ _ R1 H1). apply H1. clear H1.
  assert (n' <> m'). intro. elim H. rewrite H1. auto. apply (IHn' m' H1 H0).
Qed.

Lemma ord16 : forall n m : nat, ble_nat n m <> true -> inc m < inc n.
Proof.
  intro. induction n as [ | n' ]. intros. simpl. simpl in H. elim H. auto.
  induction m as [| m']. intro. assert (inc 0 = R0). simpl. auto. rewrite H0; clear H0.
  apply (ord5' n'). simpl. simpl in IHm'. intro. 
  assert ((inc m' < inc n') -> (inc m' + R1 < inc n' + R1)).
  intros. apply (ord8 _ _ R1 H0). apply H0; clear H0. apply (IHn' m' H).
Qed.

Lemma ord17 : forall n m : nat, ble_nat n m = true -> inc n <= inc m.
Proof.
  intro. induction n as [| n']. intros. simpl. apply ord5.
  intro. induction m as [| m']. intros. simpl in H. assert (true = false). 
  rewrite H. auto. assert (H1 := diff_true_false H0). elim H1.
  simpl. intro. assert ((inc m' >= inc n') -> (inc m' + R1 >= inc n' + R1)).
  intros. apply (ord_plus _ _ R1 H0). apply H0; clear H0. apply (IHn' m' H).
Qed.


(*絶対値の定義と性質*)
Definition abs (a b:R) := (a >= R0 /\ a = b) \/ (a <= R0 /\ - a = b).

(*bはaの絶対値である*)
(*このように実数に関する関数はここでは関係を用いて定義する*)


Lemma abs1 : forall a b:R, abs a b -> b >= R0.
Proof.
  intros. unfold abs in H. elim H.
  intros. elim H0; clear H0; intros. rewrite H1 in H0. auto.
  intros. elim H0; clear H0; intros. assert (H2 := ord_plus _ _ (- a) H0).
  rewrite (plus_0_l _) in H2; rewrite (plus_opp_r) in H2. rewrite H1 in H2. auto.
Qed.

Lemma abs2 : forall a b c d e, abs a b -> abs c d -> abs (a + c) e -> e <= b + d.
Proof.
  intros. unfold abs in H. unfold abs in H0. unfold abs in H1.
  elim H; clear H. intro. elim H; clear H; intros.
  elim H0; clear H0. intro. elim H0; clear H0; intros.
  elim H1; clear H1. intro. elim H1; clear H1; intros.
  rewrite <- H4. rewrite H2. rewrite H3. apply (ord_ref (b + d)).
  intro.  elim H1; clear H1; intros.
  assert (H5 := ord9 _ _ _ _ H H0). rewrite (plus_0_r R0) in H5. assert (H6 := ord_asym _ _ H1 H5).
  rewrite <- H2; rewrite <- H3; rewrite <- H4; rewrite H6. rewrite <- minus5. apply (ord_ref R0).
  intro. elim H0; clear H0; intros.
  elim H1; clear H1. intro. elim H1; clear H1; intros.
  rewrite <- H4. rewrite H2. apply (ord9 b b c d (ord_ref b)). rewrite <- H3.
  assert (H5 := ord_plus c R0 (- c) H0). rewrite (plus_0_l _) in H5; rewrite (plus_opp_r c) in H5.
  apply (ord_trans _ _ _ H0 H5).
  intro. elim H1; clear H1; intros.
  rewrite <- H4. rewrite <- H2. rewrite <- H3.
  rewrite (minus1 _). rewrite (distrib_r). rewrite <- minus1. rewrite <- minus1.
  assert (H5 := ord_plus _ _ (- a) H).
  rewrite plus_opp_r in H5. rewrite plus_0_l in H5. assert (H6 := ord_trans _ _ _ H5 H).
  apply (ord9 _ _ _ _ H6 (ord_ref (- c))).

  intro. elim H; clear H; intros.
  elim H0; clear H0. intro. elim H0; clear H0; intros.
  elim H1; clear H1. intro. elim H1; clear H1; intros.
  rewrite <- H4. rewrite <- H2. rewrite <- H3.
  assert (H5 := ord_plus _ _ (- a) H).
  rewrite plus_opp_r in H5. rewrite plus_0_l in H5. assert (H6 := ord_trans _ _ _ H H5).
  apply (ord9 _ _ _ _ H6 (ord_ref c)).
  intro.  elim H1; clear H1; intros.
  rewrite <- H4. rewrite <- H2. rewrite <- H3.
  rewrite (minus1 _). rewrite (distrib_r). rewrite <- minus1. rewrite <- minus1.
  assert (H5 := ord_plus _ _ (- c) H0).
  rewrite plus_opp_r in H5. rewrite plus_0_l in H5. assert (H6 := ord_trans _ _ _ H5 H0).
  apply (ord9 _ _ _ _ (ord_ref (- a)) H6).
  intro. elim H0; clear H0; intros.
  elim H1; clear H1. intro. elim H1; clear H1; intros.
  rewrite <- H4. rewrite <- H2. rewrite <- H3.
  assert (H5 := ord_plus _ _ (- a) H).
  rewrite plus_opp_r in H5. rewrite plus_0_l in H5. assert (H6 := ord_trans _ _ _ H H5).
  assert (H7 := ord_plus _ _ (- c) H0).
  rewrite plus_opp_r in H7. rewrite plus_0_l in H7. assert (H8 := ord_trans _ _ _ H0 H7).
  apply (ord9 _ _ _ _ H6 H8).
  intro. elim H1; clear H1; intros.
  rewrite <- H4. rewrite <- H2. rewrite <- H3.
  rewrite (minus1 _). rewrite (distrib_r). rewrite <- minus1. rewrite <- minus1.
  apply ord_ref.
Qed.

Lemma abs3 : forall a:R, exists b:R, abs a b.
Proof.
  intros. unfold abs. elim (total_ord a R0).
  intro. exists (- a). right. split. auto. auto. 
  intro. exists a. left. split. auto. auto.
Qed.

Lemma abs4 : forall a b c, abs a b -> abs a c -> b = c.
Proof.
  unfold abs. intros. elim H; clear H. elim H0; clear H0.
  intros. elim H; clear H; intros. elim H0; clear H0; intros. rewrite <- H1. rewrite H2. auto.
  intros. elim H; clear H; intros. elim H0; clear H0; intros. assert (H3 := ord_asym _ _ H H0).
  rewrite H3 in H1. rewrite H3 in H2. rewrite <- H1. rewrite <- H2. apply minus5.
  elim H0; clear H0. intros. elim H; clear H; intros. elim H0; clear H0; intros.
  assert (H3 := ord_asym _ _ H0 H).
  rewrite H3 in H1. rewrite H3 in H2. rewrite <- H1. rewrite <- H2. rewrite <- minus5. auto.
  intros. elim H; clear H; intros. elim H0; clear H0; intros. rewrite <- H1. rewrite H2. auto.
Qed.

Lemma abs5 : forall a, abs a R0 -> a = R0.
Proof.
  intros. unfold abs in H. elim H; clear H. intro. elim H; clear H; intros. auto.
  intro. elim H; clear H; intros. assert (- - a = - R0). rewrite H0. auto. rewrite minus3 in H1.
  rewrite H1. rewrite <- minus5. auto.
Qed.

Lemma abs6 : forall a b, abs a b -> abs (- a) b.
Proof.
  unfold abs. intros. elim H; clear H. intro H; elim H; clear H; intros.
  right. split. assert (H1 := ord_plus _ _ (- a) H). rewrite plus_opp_r in H1. 
  rewrite plus_0_l in H1. auto. rewrite minus3. auto.
  intro H; elim H; clear H; intros. left; split. assert (H1 := ord_plus _ _ (- a) H).
  rewrite plus_opp_r in H1. rewrite plus_0_l in H1. auto. auto.
Qed.

Lemma abs7 : forall a b c d e, abs a b -> abs c d -> abs (a + c) e -> b - d <= e.
Proof.
  intros. assert (H2 := abs6 _ _ H0). assert (abs (a + c - c) b). rewrite plus_assoc.
  rewrite plus_opp_r. rewrite plus_0_r. auto.
  assert (H4 := ord_plus _ _ (- d) (abs2 _ _ _ _ _ H1 H2 H3)).
  rewrite plus_assoc in H4. rewrite plus_opp_r in H4. rewrite plus_0_r in H4. auto.
Qed.


(*Archimedesの原理*)
Proposition Archimedean_property : forall x:R, exists n:nat, x < inc(n).
(*任意の実数に対し、それよりも大きい自然数が存在する*)
Proof.
  (*
    背理法による
    ある実数xに対して全ての自然数がx以下であると仮定すると、自然数全体の集合が上に有界となり、
    連続性の公理より上限x0が存在する
    x0-1より大きい自然数x1を取るとx1+1はx0より大きくなるため矛盾
  *)
  intro. elim (notAorA (forall n:nat, x >= inc n)).
  intro. assert (H0 := not_forall nat (fun n:nat => x >= inc n) H). clear H.
  elim H0. clear H0. intros. exists x0. elim (total_ord x (inc x0)).
  assert (H1 := ord2 (inc x0) x H). intro. split. auto. elim H1. intros. auto.
  intro. elim H. auto.
  intro. set (A := (fun x:R => exists n:nat, x = inc n)).
  assert (bounded_above A /\ (exists x:R, A x)). split.
  unfold bounded_above. exists x. unfold is_upper_bound. intros.
  unfold A in H0. elim H0. clear H0. intros. rewrite H0. apply (H x1).
  exists R0. unfold A. exists 0. auto.
  elim H0. clear H0. intros. assert (H2 := continuity_of_real_numbers A H0 H1). clear H0 H1.
  elim H2. clear H2. intros. unfold is_sup in H0. elim H0; clear H0; intros.
  elim (notAorA (exists n:nat, x0 - R1 < inc n)).
  intro. assert (H3 := not_exists nat (fun n:nat => x0 - R1 < inc n) H2); clear H2.
  simpl in H3. assert (is_upper_bound A (x0 - R1)). unfold is_upper_bound. intros.
  unfold A in H2. elim H2; clear H2; intros. rewrite H2. assert (H4 := ord3 (x0 - R1) (inc x2) (H3 x2)). auto.
  assert (H4 := H1 (x0 - R1) H2). assert (H5 := ord_plus x0 (x0 - R1) (R1 - x0) H4).
  rewrite (plus_assoc x0 (- R1) (R1 - x0)) in H5. rewrite <- (plus_assoc (- R1) R1 (- x0)) in H5.
  rewrite (plus_opp_l R1) in H5. rewrite (plus_0_l (- x0)) in H5. rewrite (plus_opp_r x0) in H5.
  rewrite (plus_comm R1 (- x0)) in H5. rewrite <- (plus_assoc x0 (-x0)) in H5. rewrite (plus_opp_r x0) in H5.
  rewrite (plus_0_l R1) in H5. assert (H6 := ord4). elim H6; clear H6; intros. elim H7.
  assert (H8 := ord_asym R0 R1 H6 H5). auto.
  intro. elim H2; clear H2; intros. unfold is_upper_bound in H0.
  assert (A (inc (x1) + R1)). unfold A. exists (S x1). auto.
  assert (H4 := H0 (inc x1 + R1) H3). assert (H5 := ord_plus (inc x1 + R1) x0 (- R1) H4).
  rewrite (plus_assoc (inc x1) R1 (- R1)) in H5. rewrite (plus_opp_r R1) in H5. rewrite (plus_0_r (inc x1)) in H5.
  elim H2; clear H2; intros. elim H6. apply (ord_asym (x0 - R1) (inc x1) H2 H5).
Qed.


(*位相的性質*)
Definition eps_nbd (x:R) (eps:R) (y:R) := forall a:R, abs (x - y) a -> a < eps.
Definition open (E:R -> Prop) := forall x:R, E x -> exists eps:R, eps > R0 /\ forall y:R, eps_nbd x eps y -> E y.
Definition closed (E:R -> Prop) := forall x:R, ~ E x -> exists eps:R, eps > R0 /\ forall y:R, eps_nbd x eps y -> ~ E y.

Definition covering (E:R -> Prop) (U:(R -> Prop) -> Prop) := forall x:R, E x -> exists F:R -> Prop, U F /\ F x.
Definition covering_setlist (E:R -> Prop) (U:list (R -> Prop)) :=
  forall x:R, E x -> exists F:R -> Prop, In (R -> Prop) U F /\ F x.
Definition open_family (U:(R -> Prop) -> Prop) := forall E:R -> Prop, U E -> open E.
Definition cpt (E:R -> Prop) := forall U:(R -> Prop) -> Prop, covering E U -> open_family U ->
  exists V:list (R -> Prop), (forall F:R -> Prop, In (R -> Prop) V F -> U F) /\ covering_setlist E V.

(*実数の部分集合族の型は (R -> Prop) -> Prop を用いる*)
(*開被覆の部分開被覆はRの開集合のリストで開被覆に含まれるものとして定義する*)



(*Heine-Borelの定理の証明*)

Lemma cpt1 : forall E:R -> Prop, cpt E -> bounded E.
(*コンパクト集合は有界*)
Proof.
  intros. elim (AornotA (eqset E (fun x:R => False))).

  (*Eが空のとき*)
  intro. unfold eqset in H0. elim H0. clear H0. intros _ H0. unfold included in H0.
  unfold bounded. split.
  unfold bounded_above. exists R0. unfold is_upper_bound. intros. elim (H0 x H1).
  unfold bounded_below. exists R0. unfold is_lower_bound. intros. elim (H0 x H1).

  (*Eが空でないとき*)
  (*Eの元xをとる*)
  intro. unfold eqset in H0. 
  assert (H1 := not_and_or (included E (fun _ : R => False)) (included (fun _ : R => False) E) H0).
  clear H0. elim H1. clear H1.
  intro. unfold included in H0. assert (H1 := not_forall R (fun x:R => False -> E x) H0). clear H0.
  elim H1. clear H1. intros. elim H0. intro. elim H1.
  clear H1. intro. unfold included in H0. assert (H1 := not_forall R (fun x:R => E x -> False) H0). clear H0.
  elim H1. clear H1. intros. assert (H1 := neg_elim (E x) H0). clear H0.

  (*xの半径nの開近傍の集合をAとする*)
  unfold cpt in H. set (A := (fun E:R -> Prop => exists n:nat, eqset E (eps_nbd x (inc n)))).

  (*AはEの開被覆*)
  assert (covering E A /\ open_family A). split.

  (*Aは開集合族*)
  unfold covering. intros.
  assert (H2 := Archimedean_property (x - x0)). elim H2; clear H2; intros.
  assert (H3 := Archimedean_property (x0 - x)). elim H3; clear H3; intros.
  elim (total_ord (inc x1) (inc x2)).
  intro. exists (eps_nbd x (inc x2)). split. unfold A. exists x2. unfold eqset. split.
  unfold included. intros. auto. unfold included. intros. auto.
  unfold eps_nbd. intro.
  intros. unfold abs in H5. elim H5; clear H5.
  intro. elim H5; clear H5; intros. rewrite <- H6.
  elim H2; clear H2; intros. split. apply (ord_trans _ _ _ H2 H4).
  intro. elim H7. rewrite <- H8 in H4. apply (ord_asym _ _ H2 H4).
  intro. elim H5; clear H5; intros. rewrite <- H6.
  rewrite minus4. auto.
  intro. exists (eps_nbd x (inc x1)). split. unfold A. exists x1. unfold eqset. split.
  unfold included. intros. auto. unfold included. intros. auto.
  unfold eps_nbd.
  intros. unfold abs in H5. elim H5; clear H5.
  intro. elim H5; clear H5; intros. rewrite <- H6. auto.
  intro. elim H5; clear H5; intros. rewrite <- H6. rewrite minus4.
  elim H3; clear H3; intros. split. apply (ord_trans _ _ _ H3 H4).
  intro. elim H7. rewrite <- H8 in H4. apply (ord_asym _ _ H3 H4).

  (*AはEの被覆*)
  unfold open_family. intros. unfold open. intros.
  unfold A in H0. elim H0; clear H0; intros. assert (H3 := abs3 (x - x0)).
  elim H3; clear H3; intros. exists (inc x1 - x2). split.
  unfold eqset in H0. unfold included in H0. elim H0; clear H0; intros H0 H0'.
  assert (H4 := H0' x0 H2). unfold eps_nbd in H4. assert (H5 := H4 x2 H3).
  apply ord11. assert (H6 := ord8 _ _ (- x2) H5). rewrite plus_opp_r in H6. auto.
  intros. unfold eps_nbd in H4.
  unfold eqset in H0. unfold included in H0. elim H0; clear H0; intros. apply (H0 y).
  assert (H6 := H5 x0 H2). unfold eps_nbd in H6.
  unfold eps_nbd. intros.
  assert (H8 := (H6 x2 H3)). assert (H9 := abs3 (x0 - y)). elim H9; clear H9; intros.
  assert (H10 := (H4 x3 H9)). assert (abs ((x - x0) + (x0 - y)) a).
  rewrite (plus_assoc x (- x0) (x0 - y)). rewrite <- (plus_assoc (- x0) x0 (- y)). rewrite (plus_opp_l x0).
  rewrite (plus_0_l (- y)). auto.
  assert (H12 := (abs2 _ _ _ _ _ H3 H9 H11)). assert (H13 := ord8 _ _ x2 H10).
  rewrite (plus_comm x3 x2) in H13. rewrite plus_assoc in H13. rewrite plus_opp_l in H13. rewrite plus_0_r in H13.
  elim H13; clear H13; intros. split. apply (ord_trans _ _ _ H12 H13). intro; elim H14.
  rewrite H15 in H12. apply (ord_asym _ _ H13 H12).

  (*Aの有限部分開被覆V(リスト)をとる*)
  elim H0; clear H0; intros. assert (H3 := H A H0 H2). elim H3; clear H3; intros V H3.
  elim H3; clear H3; intros.
  apply (Hilbert (covering_setlist E V) (bounded E)). auto. clear H4.

  (*ある自然数nでVの任意の元の半径以上のものが存在する*)
  (*リストVに関する帰納法により示す*)
  assert (exists n:nat, forall G:R -> Prop, In (R -> Prop) V G -> 
    forall n':nat, eqset G (eps_nbd x (inc n')) -> (ble_nat n' n) = true).
  induction V as [ | F' V']. simpl. exists 0. intros. elim H4.

  simpl. simpl in H3. assert (forall F : R -> Prop, In (R -> Prop) V' F -> A F).
  intros. apply (H3 F (or_intror H4)). assert (H5 := IHV' H4).
  elim H5; clear H5; intros n' H5. assert (H6 := H3 F' (or_introl (equal (R -> Prop) F'))).
  unfold A in H6. elim H6; clear H6; intros n'' H6. elim (AornotA (ble_nat n' n'' = true)).

  (*リストに追加する元の半径をn''、元々のリストV'の元の半径の最大値をn'をとして、n'<=n''の場合*)
  intros. exists n''. intros. elim H8; clear H8.
  intros. rewrite H8 in H9.
  assert (H10 := eqset_trans _ _ _ (eqset_sym _ _ H9) H6).
  assert (n'0 = n''). apply (neg_elim _). intro. elim (AornotA ((ble_nat n'0 n'') = true)).
  intro. unfold eqset in H10. unfold included in H10. elim H10; clear H10; intros.
  assert (eps_nbd x (inc n'') (x + inc n'0)). unfold eps_nbd.
  intros. rewrite minus1 in H14. rewrite distrib_r in H14. rewrite <- minus1 in H14. 
  rewrite <- minus1 in H14. rewrite <- plus_assoc in H14. rewrite plus_opp_r in H14.
  rewrite plus_0_l in H14. unfold abs in H14. elim H14; clear H14. intro.
  elim H14; clear H14; intros. assert (H16 := ord5 n'0). assert (H17 := ord5 n'').
  assert (H18 := ord_plus _ _ (- inc n'0) H16). rewrite plus_opp_r in H18. rewrite plus_0_l in H18.
  rewrite <- H15. split. apply (ord_trans _ _ _ H18 H17). intro. rewrite H19 in H18.
  assert (H20 := ord_asym _ _ H18 H17). rewrite H20 in H19. assert (inc n'0 - inc n'0 = inc n'0 + R0).
  rewrite H19. auto. rewrite plus_opp_r in H21. rewrite plus_0_r in H21. assert (H22 := ord5'' n'' H20).
  assert (inc n'0 = R0). rewrite H21. auto. assert (H24 := ord5'' n'0 H23). elim H11. rewrite H24. rewrite <- H22. auto.
  intro. elim H14; clear H14; intros. rewrite (minus3 (inc n'0)) in H15. rewrite <- H15. apply (ord15 _ _ H11 H12).
  assert (H15 := H10 (x + inc n'0) H14). unfold eps_nbd in H15.
  rewrite minus1 in H15. rewrite distrib_r in H15. rewrite <- minus1 in H15.
  rewrite <- minus1 in H15. rewrite <- plus_assoc in H15. rewrite plus_opp_r in H15.
  rewrite plus_0_l in H15. assert (abs (- inc n'0) (inc n'0)). unfold abs. right.
  split. assert (H16 := ord_plus _ _ (- inc n'0) (ord5 n'0)). rewrite plus_opp_r in H16.
  rewrite plus_0_l in H16. auto. rewrite (minus3 (inc n'0)). auto.
  assert (H17 := H15 (inc n'0) H16). elim H17; clear H17; intros. elim H18. auto.
  intros. unfold eqset in H10. unfold included in H10. elim H10; clear H10; intros.
  assert (eps_nbd x (inc n'0) (x + inc n'')). unfold eps_nbd.
  intros. rewrite minus1 in H14. rewrite distrib_r in H14. rewrite <- minus1 in H14. 
  rewrite <- minus1 in H14. rewrite <- plus_assoc in H14. rewrite plus_opp_r in H14.
  rewrite plus_0_l in H14. unfold abs in H14. elim H14; clear H14. intro.
  elim H14; clear H14; intros. assert (H16 := ord5 n''). assert (H17 := ord_plus _ _ (inc n'') H14).
  rewrite plus_opp_l in H17. rewrite plus_0_l in H17. assert (H18 := ord_asym _ _ H17 H16).
  assert (n'' = 0). induction n''. auto. assert (H19 := ord5' n''). elim H19; clear H19; intros.
  elim H20. rewrite H18. auto. rewrite <- H15. rewrite H19. simpl. rewrite <- minus5.
  assert (exists m:nat, n'0 = S m). apply (neg_elim _). intro.
  assert (H21 := not_exists nat (fun m:nat => n'0 = S m) H20).
  simpl in H21. elim H12. assert (n'0 = 0). induction n'0. auto. assert (H22 := H21 n'0).
  elim H22. auto. rewrite H19. rewrite H22. simpl. auto.
  elim H20; clear H20; intros. rewrite H20. apply (ord5' x0).
  intro. elim H14; clear H14; intros. rewrite minus3 in H15. rewrite <- H15. apply (ord16 _ _ H12).
  assert (H15 := H13 (x + inc n'') H14). unfold eps_nbd in H15.
  rewrite minus1 in H15. rewrite distrib_r in H15. rewrite <- minus1 in H15.
  rewrite <- minus1 in H15. rewrite <- plus_assoc in H15. rewrite plus_opp_r in H15.
  rewrite plus_0_l in H15. assert (abs (- inc n'') (inc n'')). unfold abs. right.
  split. assert (H16 := ord_plus _ _ (- inc n'') (ord5 n'')). rewrite plus_opp_r in H16.
  rewrite plus_0_l in H16. auto. rewrite (minus3 (inc n'')). auto.
  assert (H17 := H15 (inc n'') H16). elim H17; clear H17; intros. elim H18. auto.
  rewrite H11. apply (nat_ref n'').
  intro. assert (H10 := H5 G H8 n'0 H9). apply (nat_trans _ _ _ H10 H7).

  (*n'>n''の場合*)
  intros. exists n'. intros. elim H8; clear H8.
  intros. rewrite H8 in H9.
  assert (H10 := eqset_trans _ _ _ (eqset_sym _ _ H9) H6).
  assert (n'0 = n''). apply (neg_elim _). intro. elim (AornotA ((ble_nat n'0 n'') = true)).
  intro. unfold eqset in H10. unfold included in H10. elim H10; clear H10; intros.
  assert (eps_nbd x (inc n'') (x + inc n'0)). unfold eps_nbd.
  intros. rewrite minus1 in H14. rewrite distrib_r in H14. rewrite <- minus1 in H14. 
  rewrite <- minus1 in H14. rewrite <- plus_assoc in H14. rewrite plus_opp_r in H14.
  rewrite plus_0_l in H14. unfold abs in H14. elim H14; clear H14. intro.
  elim H14; clear H14; intros. assert (H16 := ord5 n'0). assert (H17 := ord5 n'').
  assert (H18 := ord_plus _ _ (- inc n'0) H16). rewrite plus_opp_r in H18. rewrite plus_0_l in H18.
  rewrite <- H15. split. apply (ord_trans _ _ _ H18 H17). intro. rewrite H19 in H18.
  assert (H20 := ord_asym _ _ H18 H17). rewrite H20 in H19. assert (inc n'0 - inc n'0 = inc n'0 + R0).
  rewrite H19. auto. rewrite plus_opp_r in H21. rewrite plus_0_r in H21. assert (H22 := ord5'' n'' H20).
  assert (inc n'0 = R0). rewrite H21. auto. assert (H24 := ord5'' n'0 H23). elim H11. rewrite H24. rewrite <- H22. auto.
  intro. elim H14; clear H14; intros. rewrite (minus3 (inc n'0)) in H15. rewrite <- H15. apply (ord15 _ _ H11 H12).
  assert (H15 := H10 (x + inc n'0) H14). unfold eps_nbd in H15.
  rewrite minus1 in H15. rewrite distrib_r in H15. rewrite <- minus1 in H15.
  rewrite <- minus1 in H15. rewrite <- plus_assoc in H15. rewrite plus_opp_r in H15.
  rewrite plus_0_l in H15. assert (abs (- inc n'0) (inc n'0)). unfold abs. right.
  split. assert (H16 := ord_plus _ _ (- inc n'0) (ord5 n'0)). rewrite plus_opp_r in H16.
  rewrite plus_0_l in H16. auto. rewrite (minus3 (inc n'0)). auto.
  assert (H17 := H15 (inc n'0) H16). elim H17; clear H17; intros. elim H18. auto.
  intros. unfold eqset in H10. unfold included in H10. elim H10; clear H10; intros.
  assert (eps_nbd x (inc n'0) (x + inc n'')). unfold eps_nbd.
  intros. rewrite minus1 in H14. rewrite distrib_r in H14. rewrite <- minus1 in H14. 
  rewrite <- minus1 in H14. rewrite <- plus_assoc in H14. rewrite plus_opp_r in H14.
  rewrite plus_0_l in H14. unfold abs in H14. elim H14; clear H14. intro.
  elim H14; clear H14; intros. assert (H16 := ord5 n''). assert (H17 := ord_plus _ _ (inc n'') H14).
  rewrite plus_opp_l in H17. rewrite plus_0_l in H17. assert (H18 := ord_asym _ _ H17 H16).
  assert (n'' = 0). induction n''. auto. assert (H19 := ord5' n''). elim H19; clear H19; intros.
  elim H20. rewrite H18. auto. rewrite <- H15. rewrite H19. simpl. rewrite <- minus5.
  assert (exists m:nat, n'0 = S m). apply (neg_elim _). intro.
  assert (H21 := not_exists nat (fun m:nat => n'0 = S m) H20).
  simpl in H21. elim H12. assert (n'0 = 0). induction n'0. auto. assert (H22 := H21 n'0).
  elim H22. auto. rewrite H19. rewrite H22. simpl. auto.
  elim H20; clear H20; intros. rewrite H20. apply (ord5' x0).
  intro. elim H14; clear H14; intros. rewrite minus3 in H15. rewrite <- H15. apply (ord16 _ _ H12).
  assert (H15 := H13 (x + inc n'') H14). unfold eps_nbd in H15.
  rewrite minus1 in H15. rewrite distrib_r in H15. rewrite <- minus1 in H15.
  rewrite <- minus1 in H15. rewrite <- plus_assoc in H15. rewrite plus_opp_r in H15.
  rewrite plus_0_l in H15. assert (abs (- inc n'') (inc n'')). unfold abs. right.
  split. assert (H16 := ord_plus _ _ (- inc n'') (ord5 n'')). rewrite plus_opp_r in H16.
  rewrite plus_0_l in H16. auto. rewrite (minus3 (inc n'')). auto.
  assert (H17 := H15 (inc n'') H16). elim H17; clear H17; intros. elim H18. auto.
  rewrite H11. assert (H12 := nat_total_ord n'' n'). elim H12; clear H12.
  intro. auto. intro. elim H7. auto.
  intro. assert (H10 := H5 G H8 n'0 H9). auto. elim H4; clear H4; intros n H4.


  intro. unfold bounded. split.

  (*x+nはEの上界*)
  unfold bounded_above. 
  exists (x + inc n). unfold is_upper_bound. intros.
  unfold covering_setlist in H5. assert (H7 := H5 x0 H6).
  elim H7; clear H7; intros F H7. elim H7; clear H7; intros.
  assert (H9 := H3 F H7). unfold A in H9. elim H9; clear H9; intros n0 H9.
  assert (H10 := H4 F H7 n0 H9). unfold eqset in H9. unfold included in H9.
  elim H9; clear H9; intros. assert (H12 := H11 x0 H8).
  unfold eps_nbd in H12. unfold abs in H12. assert (H13 := ord17 _ _ H10).
  elim (total_ord R0 (x - x0)). intro. assert (H15 := ord5 n).
  assert (H16 := ord_plus _ _ x0 (ord9 _ _ _ _ H14 H15)).
  rewrite (plus_assoc x _ _) in H16. rewrite (plus_comm (- x0) _) in H16.
  rewrite (plus_assoc x _ _) in H16. rewrite (plus_assoc (inc n) _ _) in H16.
  rewrite plus_opp_l in H16. rewrite plus_0_r in H16. rewrite plus_0_r in H16. rewrite plus_0_l in H16. auto.
  intro. assert (- (x - x0) = - (x - x0)). auto.
  assert (H16 := H12 (- (x - x0)) (or_intror (conj H14 H15))).
  rewrite minus4 in H16. elim H16; clear H16; intros.
  assert (H18 := ord_plus _ _ x (ord_trans _ _ _ H16 H13)).
  rewrite (plus_comm (inc n) _) in H18. rewrite plus_assoc in H18. rewrite plus_opp_l in H18.
  rewrite plus_0_r in H18. auto.

  (*x-nはEの下界*)
  unfold bounded_below.
  exists (x - inc n). unfold is_lower_bound. intros.
  unfold covering_setlist in H5. assert (H7 := H5 x0 H6).
  elim H7; clear H7; intros F H7. elim H7; clear H7; intros.
  assert (H9 := H3 F H7). unfold A in H9. elim H9; clear H9; intros n0 H9.
  assert (H10 := H4 F H7 n0 H9). unfold eqset in H9. unfold included in H9.
  elim H9; clear H9; intros. assert (H12 := H11 x0 H8).
  unfold eps_nbd in H12. unfold abs in H12. assert (H13 := ord17 _ _ H10).
  elim (total_ord R0 (x - x0)). intro. assert (x - x0 = x - x0). auto.
  assert (H16 := H12 (x - x0) (or_introl (conj H14 H15))).
  elim H16; clear H16; intros. assert (H18 := ord_trans _ _ _ H16 H13).
  assert (H19 := ord_plus _ _ (x0 - inc n) H18).
  rewrite (plus_assoc  x _ _) in H19. rewrite <- (plus_assoc (- x0) _ _) in H19. rewrite plus_opp_l in H19.
  rewrite plus_0_l in H19. rewrite (plus_comm x0 _) in H19. rewrite <- plus_assoc in H19. rewrite plus_opp_r in H19. 
  rewrite plus_0_l in H19. auto.
  intro. assert (H15 := ord5 n).
  assert (H16 := ord_plus _ _ (x0 - inc n) (ord9 _ _ _ _ H14 H15)).
  rewrite plus_0_l in H16. rewrite plus_0_r in H16. rewrite (plus_assoc  x _ _) in H16.
  rewrite <- (plus_assoc (- x0) _ _) in H16. rewrite plus_opp_l in H16.
  rewrite plus_0_l in H16. rewrite (plus_comm x0 _) in H16. rewrite <- plus_assoc in H16.
  rewrite plus_opp_r in H16. rewrite plus_0_l in H16. auto.
Qed.


Lemma cpt2 : forall E:R -> Prop, cpt E -> closed E.
(*コンパクト集合は閉*)
Proof.
  (*Eの補集合の元xに対し、xの半径1/(n+1)の閉近傍の補集合の集合をAとする*)
  intros. unfold closed. intros. unfold cpt in H.
  set (A := (fun F:R -> Prop => exists n:nat,
    forall y:R, F y <-> (forall a:R, abs (x - y) a -> / inc (S n) < a))).

  (*AはEの開被覆*)
  assert (covering E A /\ open_family A). split.

  (*Aは開集合族*)
  unfold covering. intros. assert (H2 := abs3 (x - x0)). elim H2; clear H2; intros a0 H2.
  assert (H3 := Archimedean_property (/ a0)). elim H3; clear H3; intros n0 H3.
  exists (fun y:R => (forall a:R, abs (x - y) a -> / inc (S n0) < a)).
  unfold A. split. exists n0. intro. split. intro; auto. intro; auto.
  intros. assert (R0 < a). assert (H5 := abs1 _ _ H4). split.
  auto. intro. rewrite <- H6 in H4. assert (x - x0 + x0 = x0). rewrite (abs5 _ H4). rewrite plus_0_l. auto.
  rewrite plus_assoc in H7. rewrite plus_opp_l in H7. rewrite plus_0_r in H7. elim H0. rewrite H7. auto.
  assert (H6 := abs4 (x - x0) _ _ H2 H4). rewrite H6 in H3.
  assert (H7 := ord8 _ _ (inc n0) ord4). simpl. rewrite plus_0_l in H7.
  rewrite plus_comm in H7. assert (H8 := ord13 _ _ _ H3 H7).
  assert (a / (inc n0 + R1) > R0).
  assert (H9 := ord12 _ _ _ (and_l _ _ (ord11 _ _) (inverse (inc (S n0)) (ord5' n0))) H5).
  simpl in H9. rewrite mult_0_l in H9. elim H9; clear H9; intros. split. auto. auto.
  assert (H10 := ord12 _ _ _ H9 H8). rewrite <- (mult_assoc (/ a)) in H10.
  assert (a <> R0). intro. elim H5; clear H5; intros. elim H12. rewrite H11. auto.
  rewrite (mult_inv_l _ H11) in H10. rewrite mult_1_l in H10. rewrite (mult_comm a _) in H10.
  rewrite <- mult_assoc in H10. assert ((inc n0 + R1) <> R0). assert (H12 := ord5' n0). elim H12; clear H12; intros.
  intro. elim H13. simpl. rewrite H14. auto. rewrite (mult_inv_r _ H12) in H10. rewrite mult_1_l in H10. auto.

  (*AはEの被覆*)
  unfold open_family. intros. unfold open. intros.
  unfold A in H1. elim H1; clear H1; intros n0 H1.
  assert (H3 := abs3 (x - x0)). elim H3; clear H3; intros a0 H3.
  exists (a0 - / inc (S n0)). split. assert (H4 := and_l _ _ (H1 x0) H2).
  assert (H5 := H4 a0 H3). assert (H6 := ord8 _ _ (- / inc (S n0)) H5). rewrite plus_opp_r in H6.
  elim H6; clear H6; intros. split. auto. auto.
  intros. unfold eps_nbd in H4. assert (H5 := abs3 (x0 - y)). elim H5; clear H5; intros b H5.
  assert (H6 := H4 b H5). assert (forall a : R, abs (x - y) a -> / inc (S n0) < a).
  intros. assert (H8 := ord8 _ _ (/ inc (S n0) - b) H6). rewrite (plus_assoc a0 _ _) in H8.
  rewrite <- (plus_assoc (- / inc (S n0)) _ _) in H8. rewrite plus_opp_l in H8.
  rewrite plus_0_l in H8. rewrite (plus_comm _ (- b)) in H8. rewrite <- plus_assoc in H8.
  rewrite plus_opp_r in H8. rewrite plus_0_l in H8. assert (abs ((x - x0) + (x0 - y)) a).
  rewrite plus_assoc. rewrite <- (plus_assoc _ x0 _). rewrite plus_opp_l. rewrite plus_0_l. auto.
  assert (H10 := abs7 _ _ _ _ _ H3 H5 H9). split. apply (ord_trans _ _ _ (and_l _ _ H8) H10).
  intro. rewrite H11 in H8. elim H8; clear H8; intros H8 H12; elim H12; clear H12.
  apply (ord_asym _ _ H8 H10). apply (and_r _ _ (H1 y) H7).

  (*Aの有限部分開被覆V(リスト)をとる*)
  elim H1; clear H1; intros. assert (H3 := H A H1 H2). elim H3; clear H3; intros V H3.
  elim H3; clear H3; intros.
  apply (Hilbert (covering_setlist E V) (exists eps : R, eps > R0 /\ (forall y : R, eps_nbd x eps y -> ~ E y))).
  auto. clear H4.

  (*ある自然数nでVの元に対応する任意の自然数以上のものが存在する*)
  (*リストVに関する帰納法により示す*)
  assert (exists n:nat, forall G:R -> Prop, In (R -> Prop) V G -> 
    forall n':nat, (forall y:R, G y <-> (forall a : R, abs (x - y) a -> / inc (S n') < a)) -> (ble_nat n' n) = true).
  induction V as [ | F' V']. simpl. exists 0. intros. elim H4.

  simpl. simpl in H3. assert (forall F : R -> Prop, In (R -> Prop) V' F -> A F).
  intros. apply (H3 F (or_intror H4)). assert (H5 := IHV' H4).
  elim H5; clear H5; intros n' H5. assert (H6 := H3 F' (or_introl (equal (R -> Prop) F'))).
  unfold A in H6. elim H6; clear H6; intros n'' H6. elim (AornotA (ble_nat n' n'' = true)).

  (*リストに追加する元に対応する自然数をn''、元々のリストV'の元に対応する自然数の最大値をn'をとして、n'<=n''の場合*)
  intros. exists n''. intros. elim H8; clear H8.
  intros. rewrite H8 in H9.
  assert (forall y:R, forall a : R, abs (x - y) a -> (/ inc (S n'') < a) -> (/ inc (S n'0)) < a).
  intros. assert (forall a : R, abs (x - y) a -> / inc (S n'') < a).
  intros. assert (H13 := abs4 _ _ _ H10 H12). rewrite <- H13. auto.
  apply ((and_l _ _ (H9 y)) ((and_r _ _ (H6 y)) H12) a H10).
  assert (forall y:R, forall a : R, abs (x - y) a -> (/ inc (S n'0) < a) -> (/ inc (S n'')) < a).
  intros. assert (forall a : R, abs (x - y) a -> / inc (S n'0) < a).
  intros. assert (H14 := abs4 _ _ _ H11 H13). rewrite <- H14. auto.
  apply ((and_l _ _ (H6 y)) ((and_r _ _ (H9 y)) H13) a H11).
  assert (n'0 = n''). apply (neg_elim _). intro. elim (AornotA ((ble_nat n'0 n'') = true)).
  intro. assert (abs (x - (x + / inc (S n'0))) (/ inc (S n'0))). rewrite minus1. rewrite distrib_r.
  rewrite <- plus_assoc. rewrite <- minus1. rewrite plus_opp_r. rewrite plus_0_l.
  rewrite <- minus1. assert (H14 := inverse _ (ord5' n'0)). unfold abs. right. split. elim H14; clear H14; intros.
  assert (H16 := ord_plus _ _ (- / inc (S n'0)) H14). rewrite plus_opp_r in H16. rewrite plus_0_l in H16.
  auto. rewrite minus3. auto. assert (/ inc (S n'') < / inc (S n'0)). assert (H15 := ord15 _ _ H12 H13).
  assert (H16 := ord8 _ _ R1 H15).
  assert (H17 := ord12 _ _ _ (and_l _ _ (ord11 R0 (/ inc (S n'0))) (inverse _ (ord5' n'0))) 
    (ord12 _ _ _ (and_l _ _ (ord11 R0 (/ inc (S n''))) (inverse _ (ord5' n''))) H16)).
  assert (inc n'' + R1 <> R0). assert (H18 := ord5' n'').
  elim H18; clear H18; intros. intro. elim H19. simpl. rewrite H20. auto.
  assert (inc n'0 + R1 <> R0). assert (H19 := ord5' n'0).
  elim H19; clear H19; intros. intro. elim H20. simpl. rewrite H21. auto.
  simpl in H17. rewrite (mult_inv_r _ H18) in H17. rewrite mult_1_l in H17. rewrite (mult_comm (inc n'0 + R1) _) in H17.
  rewrite mult_assoc in H17. rewrite (mult_inv_r _ H19) in H17. rewrite mult_1_r in H17.
  simpl. auto.
  assert (H16 := H10 (x + / inc (S n'0)) (/ inc (S n'0)) H14 H15). elim H16; clear H16; intros. elim H17. auto.
  intro. assert (abs (x - (x + / inc (S n''))) (/ inc (S n''))). rewrite minus1. rewrite distrib_r.
  rewrite <- plus_assoc. rewrite <- minus1. rewrite plus_opp_r. rewrite plus_0_l.
  rewrite <- minus1. assert (H14 := inverse _ (ord5' n'')). unfold abs. right. split. elim H14; clear H14; intros.
  assert (H16 := ord_plus _ _ (- / inc (S n'')) H14). rewrite plus_opp_r in H16. rewrite plus_0_l in H16.
  auto. rewrite minus3. auto. assert (/ inc (S n'0) < / inc (S n'')). assert (H15 := ord16 _ _ H13).
  assert (H16 := ord8 _ _ R1 H15).
  assert (H17 := ord12 _ _ _ (and_l _ _ (ord11 R0 (/ inc (S n''))) (inverse _ (ord5' n''))) 
    (ord12 _ _ _ (and_l _ _ (ord11 R0 (/ inc (S n'0))) (inverse _ (ord5' n'0))) H16)).
  assert (inc n'0 + R1 <> R0). assert (H18 := ord5' n'0).
  elim H18; clear H18; intros. intro. elim H19. simpl. rewrite H20. auto.
  assert (inc n'' + R1 <> R0). assert (H19 := ord5' n'').
  elim H19; clear H19; intros. intro. elim H20. simpl. rewrite H21. auto.
  simpl in H17. rewrite (mult_inv_r _ H18) in H17. rewrite mult_1_l in H17. rewrite (mult_comm (inc n'' + R1) _) in H17.
  rewrite mult_assoc in H17. rewrite (mult_inv_r _ H19) in H17. rewrite mult_1_r in H17.
  simpl. auto.
  assert (H16 := H11 (x + / inc (S n'')) (/ inc (S n'')) H14 H15). elim H16; clear H16; intros. elim H17. auto.
  rewrite H12. apply nat_ref.
  intro. assert (H10 := H5 G H8 n'0 H9). apply (nat_trans _ _ _ H10 H7).

  (*n'>n''の場合*)
  intro. exists n'. intros. intros. elim H8; clear H8.
  intros. rewrite H8 in H9.
  assert (forall y:R, forall a : R, abs (x - y) a -> (/ inc (S n'') < a) -> (/ inc (S n'0)) < a).
  intros. assert (forall a : R, abs (x - y) a -> / inc (S n'') < a).
  intros. assert (H13 := abs4 _ _ _ H10 H12). rewrite <- H13. auto.
  apply ((and_l _ _ (H9 y)) ((and_r _ _ (H6 y)) H12) a H10).
  assert (forall y:R, forall a : R, abs (x - y) a -> (/ inc (S n'0) < a) -> (/ inc (S n'')) < a).
  intros. assert (forall a : R, abs (x - y) a -> / inc (S n'0) < a).
  intros. assert (H14 := abs4 _ _ _ H11 H13). rewrite <- H14. auto.
  apply ((and_l _ _ (H6 y)) ((and_r _ _ (H9 y)) H13) a H11).
  assert (n'0 = n''). apply (neg_elim _). intro. elim (AornotA ((ble_nat n'0 n'') = true)).
  intro. assert (abs (x - (x + / inc (S n'0))) (/ inc (S n'0))). rewrite minus1. rewrite distrib_r.
  rewrite <- plus_assoc. rewrite <- minus1. rewrite plus_opp_r. rewrite plus_0_l.
  rewrite <- minus1. assert (H14 := inverse _ (ord5' n'0)). unfold abs. right. split. elim H14; clear H14; intros.
  assert (H16 := ord_plus _ _ (- / inc (S n'0)) H14). rewrite plus_opp_r in H16. rewrite plus_0_l in H16.
  auto. rewrite minus3. auto. assert (/ inc (S n'') < / inc (S n'0)). assert (H15 := ord15 _ _ H12 H13).
  assert (H16 := ord8 _ _ R1 H15).
  assert (H17 := ord12 _ _ _ (and_l _ _ (ord11 R0 (/ inc (S n'0))) (inverse _ (ord5' n'0))) 
    (ord12 _ _ _ (and_l _ _ (ord11 R0 (/ inc (S n''))) (inverse _ (ord5' n''))) H16)).
  assert (inc n'' + R1 <> R0). assert (H18 := ord5' n'').
  elim H18; clear H18; intros. intro. elim H19. simpl. rewrite H20. auto.
  assert (inc n'0 + R1 <> R0). assert (H19 := ord5' n'0).
  elim H19; clear H19; intros. intro. elim H20. simpl. rewrite H21. auto.
  simpl in H17. rewrite (mult_inv_r _ H18) in H17. rewrite mult_1_l in H17. rewrite (mult_comm (inc n'0 + R1) _) in H17.
  rewrite mult_assoc in H17. rewrite (mult_inv_r _ H19) in H17. rewrite mult_1_r in H17.
  simpl. auto.
  assert (H16 := H10 (x + / inc (S n'0)) (/ inc (S n'0)) H14 H15). elim H16; clear H16; intros. elim H17. auto.
  intro. assert (abs (x - (x + / inc (S n''))) (/ inc (S n''))). rewrite minus1. rewrite distrib_r.
  rewrite <- plus_assoc. rewrite <- minus1. rewrite plus_opp_r. rewrite plus_0_l.
  rewrite <- minus1. assert (H14 := inverse _ (ord5' n'')). unfold abs. right. split. elim H14; clear H14; intros.
  assert (H16 := ord_plus _ _ (- / inc (S n'')) H14). rewrite plus_opp_r in H16. rewrite plus_0_l in H16.
  auto. rewrite minus3. auto. assert (/ inc (S n'0) < / inc (S n'')). assert (H15 := ord16 _ _ H13).
  assert (H16 := ord8 _ _ R1 H15).
  assert (H17 := ord12 _ _ _ (and_l _ _ (ord11 R0 (/ inc (S n''))) (inverse _ (ord5' n''))) 
    (ord12 _ _ _ (and_l _ _ (ord11 R0 (/ inc (S n'0))) (inverse _ (ord5' n'0))) H16)).
  assert (inc n'0 + R1 <> R0). assert (H18 := ord5' n'0).
  elim H18; clear H18; intros. intro. elim H19. simpl. rewrite H20. auto.
  assert (inc n'' + R1 <> R0). assert (H19 := ord5' n'').
  elim H19; clear H19; intros. intro. elim H20. simpl. rewrite H21. auto.
  simpl in H17. rewrite (mult_inv_r _ H18) in H17. rewrite mult_1_l in H17. rewrite (mult_comm (inc n'' + R1) _) in H17.
  rewrite mult_assoc in H17. rewrite (mult_inv_r _ H19) in H17. rewrite mult_1_r in H17.
  simpl. auto.
  assert (H16 := H11 (x + / inc (S n'')) (/ inc (S n'')) H14 H15). elim H16; clear H16; intros. elim H17. auto.
  rewrite H12. elim (nat_total_ord n' n''). intro. elim H7. auto. intro. auto.
  intro. assert (H10 := H5 G H8 n'0 H9). auto.

  elim H4; clear H4; intros n H4. intro.

  (*xの半径1/(n+1)の開近傍はEの補集合に含まれる*)
  exists (/ inc (S n)). split. apply (and_l _ _ (ord11 R0 (/ inc (S n))) (inverse (inc (S n)) (ord5' n))).
  intros. unfold covering_setlist in H5. intro.
  assert (H8 := H5 y H7). elim H8; clear H8; intros F H8. elim H8; clear H8; intros.
  assert (H10 := H3 F H8). unfold A in H10. elim H10; clear H10; intros m H10.
  assert (H11 := and_l _ _ (H10 y) H9). unfold eps_nbd in H6. assert (H12 := H4 F H8 m H10).
  assert (H13 := abs3 (x - y)). elim H13; clear H13; intros. assert (H14 := H6 x0 H13).
  assert (H15 := H11 x0 H13). assert (H16 := ord13 _ _ _ H15 H14).
  assert (H17 := ord_plus _ _ R1 (ord17 _ _ H12)).
  clear E H x H0 A H1 H2 V H3 H4 H5 y H6 H7 F H8 H9 H10 H11 H12 x0 H13 H14 H15.
  assert (inc n + R1 <> R0). assert (H := ord5' n). elim H; clear H; intros. intro. elim H0. simpl. rewrite H1. auto.
  assert (inc m + R1 <> R0). assert (H0 := ord5' m). elim H0; clear H0; intros. intro. elim H1. simpl. rewrite H2. auto.
  assert (H1 := ord12 _ _ _ (and_l _ _ (ord11 R0 (inc (S n))) (ord5' n)) 
    (ord12 _ _ _ (and_l _ _ (ord11 R0 (inc (S m))) (ord5' m)) H16)). simpl in H1.
  rewrite (mult_inv_l _ H0) in H1. rewrite mult_1_l in H1. rewrite (mult_comm _ (inc m + R1)) in H1.
  rewrite mult_assoc in H1. rewrite (mult_inv_l _ H) in H1. rewrite mult_1_r in H1.
  elim H1; clear H1; intros. elim H2. apply (ord_asym _ _ H1 H17).
Qed.


Lemma cpt3 : forall a b : R, cpt (fun c : R => a <= c <= b).
(*有界閉区間はコンパクト*)
Proof.
  (*区間縮小法は用いない*)
  intros. unfold cpt. intros.

  (*b<aのとき*)
  elim (notAorA (a <= b)).
  intro. exists (nil (R -> Prop)).
  split. intros. simpl in H2. elim H2.
  unfold covering_setlist. intros. elim H2; clear H2; intros. elim H1.
  apply (ord_trans _ _ _ H2 H3).

  (*a<=bのとき*)
  intro.

  (*a<=c<=bで、[a,c]に対し、Uの有限部分被覆が取れるc全体をKとおく*)
  set (K := fun d:R => a <= d <= b /\ (exists V : list (R -> Prop),
  (forall F : R -> Prop, In (R -> Prop) V F -> U F) /\
  covering_setlist (fun c : R => a <= c <= d) V)).

  (*Kは空でなくて上に有界なので上限xが存在する*)
  assert (bounded_above K /\ K a). split.
  unfold bounded_above. exists b. unfold is_upper_bound. intros.
  unfold K in H2. elim H2; clear H2; intros. elim H2; clear H2; intros. auto.
  unfold K. split. split. apply (ord_ref a). auto.
  unfold covering in H. assert (H2 := H a (conj (ord_ref a) H1)). elim H2; clear H2; intros.
  exists (cons (R -> Prop) x (nil (R -> Prop))). split. intros.
  unfold In in H3. elim H3. intro. rewrite H4. elim H2; intros; auto. intro H4; elim H4.
  unfold covering_setlist. intros. elim H3; clear H3; intros H3 H4; assert (H5 := ord_asym _ _ H3 H4).
  exists x. unfold In. split. left. auto. rewrite <- H5; elim H2; intros; auto.
  elim H2; clear H2; intros. assert (exists x:R, K x). exists a. auto.
  assert (H5 := continuity_of_real_numbers K H2 H4). clear H4.
  elim H5; clear H5; intros.

  (*xはKの元である*)
  assert (a <= x <= b).
  unfold is_sup in H4. elim H4; clear H4; intros.
  unfold is_upper_bound in H4. assert (H6 := H4 a H3). split; auto.
  assert (is_upper_bound K b). unfold is_upper_bound. intros.
  unfold K in H7. elim H7; intros H8; elim H8; intros; auto.
  assert (H8 := H5 b H7). auto.
  assert (K x). unfold K. split. auto.
  unfold covering in H. assert (H6 := H x H5).
  elim H6; clear H6; intros E H6. elim H6; clear H6; intros.
  unfold open_family in H0. assert (H8 := H0 E H6). unfold open in H8.
  assert (H9 := H8 x H7). elim H9; clear H9; intros eps H9. elim H9; clear H9; intros.
  assert (H11 := ord10 _ _ K H4 H9). elim H11; clear H11; intros. elim H11; clear H11; intros.
  unfold K in H11. elim H11; clear H11; intros. elim H13; clear H13; intros V H13.
  exists (cons (R -> Prop) E V). elim H13; clear H13; intros. split.
  intros. simpl in H15. elim H15; clear H15. intro. rewrite H15; auto.
  apply (H13 F).
  unfold covering_setlist. intros. elim (AornotA (x1 <= x0)).
  intro. unfold covering_setlist in H14. elim H15; clear H15; intros. assert (H18 := H14 x1 (conj H15 H16)).
  elim H18; clear H18; intros. exists x2. elim H18; clear H18; intros. split.
  simpl. right. auto. auto.
  intros. exists E. split. simpl. left. auto. assert (H17 := ord2 _ _ H16).
  unfold eps_nbd in H10. assert (forall a : R, abs (x - x1) a -> a < eps).
  intros. unfold abs in H18. elim H18; clear H18. intro. elim H18; clear H18; intros.
  rewrite <- H19. elim H17; clear H17; intros.
  assert (H21 := ord8 _ _ (- x0 + eps - x1) (ord7 _ _ _ _ ((and_r _ _ (ord11 (x - eps) x0)) H12) H17)).
  rewrite plus_assoc in H21. rewrite <- (plus_assoc x0 (- x0 + eps) (- x1)) in H21.
  rewrite <- (plus_assoc x0 (- x0) eps) in H21. rewrite plus_opp_r in H21. rewrite plus_0_l in H21.
  rewrite plus_assoc in H21. rewrite <- (plus_assoc (- eps) eps (- x1)) in H21.
  rewrite plus_opp_l in H21. rewrite plus_0_l in H21. rewrite (plus_comm x0 x1) in H21. rewrite plus_assoc in H21.
  rewrite <- (plus_assoc x0 (- x0 + eps) _) in H21. rewrite <- (plus_assoc x0 _ _) in H21.
  rewrite plus_opp_r in H21. rewrite plus_0_l in H21. rewrite (plus_comm eps _) in H21. rewrite <- plus_assoc in H21.
  rewrite plus_opp_r in H21. rewrite plus_0_l in H21. auto.
  intro. elim H18; clear H18; intros. assert (H21 := ord_plus _ _ (- x1) (and_r _ _ H15)). rewrite plus_opp_r in H21.
  assert (H22 := ord_asym _ _ H18 H21). rewrite H22 in H19. rewrite <- minus5 in H19. rewrite <- H19.
  apply (and_r _ _ (ord11 R0 eps)). auto. apply (H10 x1 H18).

  (*x=bのとき*)
  elim (AornotA (x = b)). intro. rewrite H7 in H6. unfold K in H6.
  elim H6; clear H6; intros. auto.

  (*x<bのとき*)
  (*
    xを含むUの元Eを取ると、E元dについては全て、
    xに対応する有限部分被覆にEを加えると[a,d]の被覆になるため、dはKに含まれる
    x<d<=bなるEの元dが必ず取れるため、xが上限であることに矛盾
    (具体的には、xのeps近傍がEに含まれるとして、d=min{x+eps/2,b}を取っている)
  *)
  intro. unfold covering in H. assert (H8 := H x H5).
  elim H8; clear H8; intros E H8. elim H8; clear H8; intros.
  unfold open_family in H0. assert (H10 := H0 E H8). unfold open in H10.
  assert (H11 := H10 x H9). elim H11; clear H11; intros eps H11. elim H11; clear H11; intros.
  elim (total_ord (x + eps / (R1 + R1)) b).
  intro. assert (K (x + eps / (inc 2))). unfold K. split. split.
  assert (H14 := ord_mult _ _ (and_l _ _ H11) (and_l _ _ (inverse _ (ord5' 1)))).
  elim H5; clear H5; intros. assert (H16 := ord9 _ _ _ _ H5 H14). rewrite plus_0_r in H16. auto.
  unfold inc. rewrite plus_0_l. auto.
  unfold K in H6. elim H6; clear H6; intros _ H6. elim H6; clear H6; intros V H6. elim H6; clear H6; intros.
  exists (cons (R -> Prop) E V). split. intros. simpl in H15. elim H15; clear H15.
  intro. rewrite H15; assumption. intro. apply (H6 F H15).
  unfold covering_setlist. intros. elim (total_ord x x0). intro. exists E. split. simpl. left. auto.
  assert (eps_nbd x eps x0). unfold eps_nbd. intros. unfold abs in H17. elim H17; clear H17.
  intro. elim H17; clear H17; intros. assert (H19 := ord_plus _ _ x0 H17). rewrite plus_assoc in H19.
  rewrite plus_opp_l in H19. rewrite plus_0_r in H19. rewrite plus_0_l in H19.
  assert (H20 := ord_asym _ _ H16 H19). rewrite H20 in H18. rewrite plus_opp_r in H18.
  rewrite <- H18. apply (and_r _ _ (ord11 R0 eps)). auto.
  intros. elim H17; clear H17; intros. rewrite minus4 in H18. rewrite <- H18.
  elim H15; clear H15; intros. assert (H20 := ord_plus _ _ (- x) H19). rewrite (plus_comm x _) in H20.
  rewrite plus_assoc in H20. rewrite plus_opp_r in H20. rewrite plus_0_r in H20.
  assert (eps / inc 2 < eps). rewrite <- (mult_1_r eps). rewrite mult_assoc. rewrite mult_comm.
  rewrite (mult_comm eps R1). apply (ord12 _ _ eps H11). apply ord14.
  elim H21; intros. split. apply (ord_trans _ _ _ H20 H22). intro. elim H23. rewrite H24 in H20.
  apply (ord_asym _ _ H22 H20). apply (H12 x0 H17).
  intro. unfold covering_setlist in H14. assert (a <= x0 <= x).
  split. elim H15; intros; auto. auto. assert (H18 := H14 x0 H17). elim H18; clear H18; intros.
  exists x1. elim H18; clear H18; intros. split. simpl. right. auto. auto.
  unfold is_sup in H4. elim H4; clear H4; intros. unfold is_upper_bound in H4.
  assert (H16 := H4 (x + eps / inc 2) H14).
  assert (H17 := ord12 R0 eps (/ inc 2) (and_l _ _ (ord11 R0 (/ inc 2))(inverse (inc 2) (ord5' 1)))
    ((and_r _ _ (ord11 R0 eps) H11))).
  rewrite mult_0_l in H17. assert (H18 := ord8 _ _ x H17). rewrite plus_0_l in H18. rewrite plus_comm in H18.
  assert (H19 := ord7 _ _ _ _ H18 H16). rewrite plus_comm in H19. elim H19; intros. elim H21. auto.
  intro. unfold K in H6. elim H6; clear H6; intros _ H6. elim H6; clear H6; intros V H6. elim H6; clear H6; intros.
  exists (cons (R -> Prop) E V). split. intros. simpl in H15. elim H15; clear H15.
  intro. rewrite H15; assumption. intro. apply (H6 F H15).
  unfold covering_setlist. intros. elim (total_ord x x0). intro. exists E. split. simpl. left. auto.
  assert (eps_nbd x eps x0). unfold eps_nbd. intros. unfold abs in H17. elim H17; clear H17.
  intro. elim H17; clear H17; intros. assert (H19 := ord_plus _ _ x0 H17). rewrite plus_assoc in H19.
  rewrite plus_opp_l in H19. rewrite plus_0_r in H19. rewrite plus_0_l in H19.
  assert (H20 := ord_asym _ _ H16 H19). rewrite H20 in H18. rewrite plus_opp_r in H18.
  rewrite <- H18. apply (and_r _ _ (ord11 R0 eps)). auto.
  intros. elim H17; clear H17; intros. rewrite minus4 in H18. rewrite <- H18.
  elim H15; clear H15; intros. assert (H20 := ord_plus _ _ (- x) H19).
  assert (H21 := ord_plus _ _ (- x) H13). rewrite (plus_comm x _) in H21.
  rewrite plus_assoc in H21. rewrite plus_opp_r in H21. rewrite plus_0_r in H21.
  assert (eps / inc 2 < eps). rewrite <- (mult_1_r eps). rewrite mult_assoc. rewrite mult_comm.
  rewrite (mult_comm eps R1). apply (ord12 _ _ eps H11). apply ord14.
  elim H22; intros. assert (H25 := ord_trans _ _ _ H20 H21). simpl in H23. rewrite plus_0_l in H23.
  split. apply (ord_trans _ _ _ H25 H23). intro. elim H24. rewrite H26 in H25. simpl. rewrite plus_0_l.
  apply (ord_asym _ _ H23 H25). apply (H12 x0 H17).
  intro. unfold covering_setlist in H14. assert (a <= x0 <= x).
  split. elim H15; intros; auto. auto. assert (H18 := H14 x0 H17). elim H18; clear H18; intros.
  exists x1. elim H18; clear H18; intros. split. simpl. right. auto. auto.
Qed.


Lemma cpt4 : forall E:R -> Prop, cpt E -> forall F:R -> Prop, included E F -> closed F -> cpt F.
(*コンパクト集合の閉集合はコンパクト*)
Proof.
  (*Fの開被覆Uに対して、UにFの補集合を付け加えてものはEの開被覆になるため、有限部分被覆が取れる*)
  intros. unfold cpt. intros. unfold cpt in H.
  set (A := fun G:R -> Prop => U G \/ (forall x:R, G x <-> ~ F x)).
  assert (covering E A /\ open_family A). split. unfold covering. intros.
  elim (AornotA (F x)). intro. unfold covering in H2.
  assert (H6 := H2 x H5). elim H6; clear H6; intros. exists x0. split.
  unfold A. left. apply (and_l _ _ H6). apply (and_r _ _ H6).
  intro. exists (fun y:R => ~ F y). split. unfold A. right. intros. split. intro; auto. intro; auto. auto.
  unfold open_family. intros. unfold A in H4. elim H4; clear H4. intro.
  unfold open_family in H3. apply (H3 E0 H4).
  intro. unfold closed in H1. unfold open. intros.
  assert (H6 := H1 x (and_l _ _ (H4 x) H5)). elim H6; clear H6; intros. elim H6; clear H6; intros.
  exists x0. split. auto. intros. apply (and_r _ _ (H4 y) (H7 y H8)).
  elim H4; clear H4; intros. assert (H6 := H A H4 H5). elim H6; clear H6; intros l H6. elim H6; clear H6.

  (*実数の部分集合のリストlに関する帰納法によりlからFの補集合だけを抜いたリストmが作れる*)
  assert (exists m: list (R -> Prop), forall G : R -> Prop,
    In (R -> Prop) m G <-> (In (R -> Prop) l G /\ ~ (forall x:R, G x <-> ~ F x))).
  induction l as [ | V l']. exists (nil (R -> Prop)).
  intro. split. intro. split. auto. simpl in H6. elim H6. intro. elim H6; intros; auto.
  elim IHl'; clear IHl'; intros n H6.
  elim (AornotA (forall x : R, V x <-> ~ F x)).
  intro. exists n. simpl. intros. assert (H8 := H6 G). elim H8; clear H8; intros.
  split. intros. assert (H11 := H8 H10). elim H11; clear H11; intros. split. right. auto. auto.
  intros. elim H10; clear H10; intros. elim H10. intro. rewrite <- H12 in H7. elim H11. auto.
  intro. apply (H9 (conj H12 H11)).
  intro. exists (cons (R -> Prop) V n). simpl. intro. assert (H8 := H6 G). elim H8; clear H8; intros.
  split. intros. split. elim H10. intro. left. auto.
  intro. right. apply (and_l _ _ (H8 H11)). elim H10. intro. rewrite H11. auto.
  intro. apply (and_r _ _ (H8 H11)).
  intro. elim H10; clear H10; intros. elim H10. intro. left. auto.
  intro. right. apply (H9 (conj H12 H11)).
  intros. elim H6; clear H6; intros m H6. exists m. split.

  (*mが実際Uに対するFの有限部分被覆であることから、Fはcpt*)
  intros. assert (H10 := (and_l _ _ (H6 F0) H9)). elim H10; clear H10; intros.
  assert (H12 := H7 F0 H10). unfold A in H12. elim H12. intro; auto. intro; elim H11; auto.
  unfold covering_setlist. intros. unfold covering_setlist in H8.
  unfold included in H0. assert (H10 := H8 x (H0 x H9)). elim H10; clear H10; intros F0 H10.
  exists F0. elim H10; clear H10; intros. split.
  assert (~ (forall x : R, F0 x <-> ~ F x)). intro. assert (H13 := and_l _ _ (H12 x) H11).
  elim H13. auto. apply (and_r _ _ (H6 F0) (conj H10 H12)). auto.
Qed.


Lemma cpt5 : forall E:R -> Prop, bounded E -> closed E -> cpt E.
(*有界閉集合はコンパクト*)
Proof.
  intros. unfold bounded in H. unfold bounded_above in H; unfold bounded_below in H.
  elim H; clear H; intros. elim H; clear H; intros b H. elim H1; clear H1; intros a H1.
  assert (H2 := cpt3 a b). assert (included (fun c : R => a <= c <= b) E).
  unfold included. intros. unfold is_upper_bound in H. unfold is_lower_bound in H1.
  apply (conj (H1 x H3) (H x H3)). apply (cpt4 (fun c : R => a <= c <= b) H2 E H3 H0).
Qed.



(*次が目的の定理である*)

Theorem Heine_Borel : forall E:R -> Prop, cpt E <-> (bounded E /\ closed E).
(*R上コンパクトと有界閉は同値*)
Proof.
  intro. split.
  intro. split. apply (cpt1 E H). apply (cpt2 E H).
  intro. elim H; clear H; intros. apply (cpt5 E H H0).
Qed.