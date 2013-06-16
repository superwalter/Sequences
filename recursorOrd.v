Require Import Bool.
Require Import EqNat.
Require Import Setoid.
Require Import Le Lt Plus Minus Compare_dec.


(*****************************************************************)
(*Compare nat returning boolean*)
(*****************************************************************)

(*****************************************************************)
(*beq_nat*)
Lemma beq_nat_sym : forall m n, beq_nat m n = beq_nat n m.
intros m n.
case_eq (beq_nat m n); intros.
 rewrite beq_nat_true_iff in H; subst m;
   rewrite (beq_nat_refl n); trivial.

 rewrite beq_nat_false_iff in H.
 case_eq (beq_nat n m); intros; trivial.
  rewrite beq_nat_true_iff in H0.
  elim H; subst n; trivial.
Qed.

(****************************************************************)
(*ltb*)
Definition ltb n m := leb (S n) m.

Lemma ltb_iff : forall m n,
  ltb m n = true <-> m < n.
unfold ltb; intros; rewrite leb_iff; split; trivial.
Qed.

Lemma ltb_eq_nat_dec : forall m n,
  {ltb m n = true} + {beq_nat m n = true} + {ltb n m = true}.
intros m n.
generalize (lt_eq_lt_dec m n); intros H.
destruct H as [[H|H]|H]; [left; left; rewrite ltb_iff|
  left; right; rewrite beq_nat_true_iff|
    right; rewrite ltb_iff]; trivial.
Qed.

Lemma ltb_leb_iff : forall m n b,
  ltb m n = b <-> leb n m = negb b.
intros m n b.
destruct b; simpl; [|unfold ltb]; rewrite leb_iff_conv;
  [rewrite ltb_iff; reflexivity|rewrite leb_iff].
 split; intros; [apply lt_n_Sm_le|
   apply le_lt_n_Sm]; trivial.
Qed.

Lemma ltb_antirefl : forall m, ltb m m = false.
unfold ltb; intro m.
rewrite leb_iff_conv.
apply lt_n_Sn.
Qed.

Lemma leb_ltb_beq_conv : forall m n, 
  leb m n = ltb m n || beq_nat m n.
intros m n.
case_eq (leb m n); intro H.
 rewrite leb_iff in H.
 rewrite le_lt_or_eq_iff in H.
 destruct H as [H|H].
  rewrite <- ltb_iff in H; rewrite H; simpl; trivial.

  subst m; rewrite <- beq_nat_refl.
  rewrite orb_true_r; trivial.

 rewrite leb_iff_conv in H.
 case_eq (ltb m n); intros H'; [|clear H']; simpl.
  rewrite ltb_iff in H'; apply lt_asym in H; contradiction.
  
  case_eq (beq_nat m n); intros H'; trivial.
   rewrite beq_nat_true_iff in H'.
   subst m; apply lt_irrefl in H; contradiction.
Qed.
  

(*****************************************************************)
(*Cantor Normal Form Ordinals*)
(*****************************************************************)
Inductive Ord : Set :=
| fin : nat -> Ord 
| inf : nat -> Ord -> Ord -> Ord.

Fixpoint degree (o : Ord) : Ord :=
  match o with
    | fin _ => fin 0
    | inf n p Q => p
  end.

Fixpoint scan (o : Ord) : bool :=
  match o with
    | fin 0 => false
    | fin (S _) => true
    | inf _ _ o' => scan o'
  end.

Definition ZeroO (o : Ord) : bool :=
  match o with
    | fin 0 => true
    | _ => false
  end.

Lemma ZeroO_fin0 : forall o, ZeroO o = true -> o = fin 0.
destruct o as [n|n p q]; simpl; intros; [
  destruct n; [trivial|discriminate]|discriminate].
Qed.

Definition SuccOFin (o : Ord) : bool :=
  match o with
    | fin (S _) => true
    | _ => false
  end.

Definition SuccOInf (o : Ord) := 
  match o with
    | inf _ _ _  => scan o
    | _ => false
  end.

Definition InfO (o : Ord) :=
  match o with
    | inf _ _ _ => negb (scan o)
    | _ => false
  end.

Definition SuccO (o : Ord) := SuccOInf o || SuccOFin o.

Lemma ord_classification : forall (o : Ord),
  {ZeroO o = true} + {SuccO o = true} + {InfO o = true}.
induction o as [n|n p _ q Hq]; simpl.
 destruct n; left; [left|right]; trivial.
 
 destruct Hq as [[HO|HS]|HI].
  apply ZeroO_fin0 in HO; subst q; right; simpl; trivial.

  left; right; unfold SuccO in HS |- *; simpl.
  destruct q; simpl in *; trivial.
   rewrite orb_false_r; trivial.

  destruct q as [m|m u v]. 
   destruct m; simpl in HI; discriminate.
   
   simpl in *; right; trivial.
Qed.


(*Equation of ordinals*)
Fixpoint beq_ord (o o' : Ord) : bool :=
  match o, o' with
    | fin m, fin n => beq_nat m n
    | inf n p Q, inf n' p' Q' =>
      (beq_nat n n') && (beq_ord p p') && (beq_ord Q Q')
    | _, _ => false
  end.

Lemma beq_ord_refl : forall o, beq_ord o o = true.
induction o; simpl; [|repeat rewrite andb_true_iff; 
  split; [split|]]; trivial; rewrite beq_nat_true_iff; trivial.
Qed.

Lemma beq_ord_eq : forall o o',
  beq_ord o o' = true <-> o = o'.
split; [revert o'|].
 induction o as [|n p Hp Q HQ]; destruct o' as [|n' p' Q']; 
   simpl; intros; [apply beq_nat_true in H; subst n; trivial|
     discriminate|discriminate|].
  repeat rewrite andb_true_iff in H.
  destruct H as ((Hnn', Hpp'), Hqq').
  apply Hp in Hpp'.
  apply HQ in Hqq'.
  apply beq_nat_true in Hnn'.
  subst n p Q; trivial.

 intros; subst o'.
 induction o; simpl; [rewrite beq_nat_true_iff; trivial|].
  repeat rewrite andb_true_iff.
  split; [split|]; trivial; rewrite beq_nat_true_iff; trivial.
Qed.


(*Order between ordinals*)
Fixpoint btb_ord (o o' : Ord) : bool :=
  match o, o' with
    | fin m, fin n => (ltb n m)
    | fin _, inf _ _ _  => false
    | inf _ _ _, fin _ => true
    | inf n p Q, inf n' p' Q' =>
      (btb_ord p p') || (beq_ord p p') && (ltb n' n) || 
        (beq_ord p p') && (beq_nat n n') && (btb_ord Q Q')
  end.


Definition beb_ord (o o' : Ord) := btb_ord o o' || beq_ord o o'.
 
Lemma btb_0 : forall o o',
  btb_ord o o' = true -> btb_ord o (fin 0) = true.
induction o as [|n p Hp Q HQ]; destruct o' as [|n' p' Q']; 
  simpl; intros; [|discriminate| |]; trivial.
 rewrite ltb_iff in *.
 apply le_lt_trans with (1:=(le_0_n n0)) (2:=(H)).
Qed.

Lemma not_0_bt_0 : forall (o : Ord),
  ZeroO o = false ->
  btb_ord o (fin 0) = true.
destruct o as [n|n p q]; simpl; trivial.
 destruct n; [discriminate|intros _].
  rewrite ltb_iff.
  apply lt_0_Sn.
Qed.

Lemma btb_antirefl : forall o, btb_ord o o = false.
induction o; simpl.
 apply ltb_antirefl.
 
 rewrite IHo1; rewrite IHo2.
 rewrite ltb_antirefl.
 repeat rewrite andb_false_r; simpl; trivial.
Qed.

Lemma btb_ord_trans : forall o1 o2 o3,
  btb_ord o1 o2 = true ->
  btb_ord o2 o3 = true ->
  btb_ord o1 o3 = true.
induction o1 as [n1|n1 p1 Hp1 q1 Hq1]; 
  destruct o2 as [n2|n2 p2 q2]; destruct o3 as [n3|n3 p3 q3]; 
    simpl; intros H12 H23; try discriminate; trivial.
 rewrite ltb_iff in H12, H23 |- *.
 apply lt_trans with (1:=H23) (2:=H12).

 repeat rewrite orb_true_iff in H12, H23 |- *.
 destruct H12 as [[H12|H12]|H12].
  left; left; destruct H23 as [[H23|H23]|H23].
   apply Hp1 with (1:=H12) (2:=H23).

   rewrite andb_true_iff in H23; destruct H23 as (H23, _).
   rewrite beq_ord_eq in H23; subst p3; trivial.

   repeat rewrite andb_true_iff in H23.
   destruct H23 as ((H23, _), _).
   rewrite beq_ord_eq in H23; subst p3; trivial.

  rewrite andb_true_iff in H12; destruct H12 as (H12, H12').
  rewrite beq_ord_eq in H12; subst p2.
  destruct H23 as [[H23|H23]|H23]; 
    [left;left|left;right|left;right]; trivial; 
      rewrite andb_true_iff in H23 |- *;
        [|rewrite andb_true_iff in H23; destruct H23 as (H23, _)];
        destruct H23 as (H23, H23');
          rewrite beq_ord_eq in H23; subst p3;
            rewrite beq_ord_eq; rewrite ltb_iff in H12' |- *.
   rewrite ltb_iff in H23'.
   split; [|apply lt_trans with (m:=n2)]; trivial.

   rewrite beq_nat_true_iff in H23'; subst n3.
   split; trivial.

  repeat rewrite andb_true_iff in H12.
  destruct H12 as ((H12_, H12'), H12).
  rewrite beq_ord_eq in H12_; subst p2.
  rewrite beq_nat_true_iff in H12'; subst n2.
  destruct H23 as [[H23|H23]|H23]; 
    [left;left|left;right|right]; trivial.
   repeat rewrite andb_true_iff in H23 |- *.
   destruct H23 as ((H23', H23_), H23).
   split; [split|apply Hq1 with (1:=H12)]; trivial.
Qed. 

Lemma beb_btb_trans : forall o1 o2 o3,
  beb_ord o1 o2 = true ->
  btb_ord o2 o3 = true ->
  btb_ord o1 o3 = true.
intros o1 o2 o3 Ho12 Ho23.
unfold beb_ord in Ho12.
rewrite orb_true_iff in Ho12.
destruct Ho12 as [Hlt|Heq];
  [apply btb_ord_trans with (1:=Hlt) (2:=Ho23) |
  rewrite beq_ord_eq in Heq; subst o2; trivial].
Qed. 

Lemma btb_beb_trans : forall o1 o2 o3,
  btb_ord o1 o2 = true ->
  beb_ord o2 o3 = true ->
  btb_ord o1 o3 = true.
intros o1 o2 o3 Ho12 Ho23.
unfold beb_ord in Ho23.
rewrite orb_true_iff in Ho23.
destruct Ho23 as [Hlt|Heq];
  [apply btb_ord_trans with (2:=Hlt) (1:=Ho12) |
  rewrite beq_ord_eq in Heq; subst o2; trivial].
Qed. 

Lemma beb_trans : forall o1 o2 o3,
  beb_ord o1 o2 = true ->
  beb_ord o2 o3 = true ->
  beb_ord o1 o3 = true.
intros o1 o2 o3 Ho12 Ho23.
unfold beb_ord in Ho12.
rewrite orb_true_iff in Ho12.
destruct Ho12 as [Hlt1|Heq1]; [unfold beb_ord;
  apply btb_beb_trans with (1:=Hlt1) in Ho23; rewrite Ho23 |
    rewrite beq_ord_eq in Heq1; subst o2]; trivial.
Qed.

Lemma btb_eq_dec : forall o o',
  {btb_ord o o'=true} + {beq_ord o o'=true} + {btb_ord o' o=true}.
induction o as [n|n p Hp q Hq]; destruct o' as [n'|n' p' q']; 
  simpl; [|right|left; left|]; trivial.
 generalize (lt_eq_lt_dec n n'); intro H.
 destruct H as [[H|H]|H]; [right; rewrite ltb_iff |
   left; right; rewrite beq_nat_true_iff |
     left; left; rewrite ltb_iff]; trivial.

 specialize Hp with (o':=p').
 specialize Hq with (o':=q').
 destruct Hp as [[Hp|Hp]|Hp]; [
   left; left; repeat rewrite orb_true_iff; left; left| |
     right; repeat rewrite orb_true_iff; left; left]; trivial.
  rewrite beq_ord_eq in Hp; subst p'.
  generalize (lt_eq_lt_dec n n'); intro H.
  destruct H as [[H|H]|H].
   right; repeat rewrite orb_true_iff; left; right.
   rewrite andb_true_iff; rewrite ltb_iff; 
     split; [apply beq_ord_refl|]; trivial.

   subst n'; destruct Hq as [[Hq|Hq]|Hq].
    left; left; repeat rewrite orb_true_iff; right.
    repeat rewrite andb_true_iff; split; [split; 
      [apply beq_ord_refl|rewrite beq_nat_true_iff]|]; trivial.

    rewrite beq_ord_eq in Hq; subst q'.
    left; right; repeat rewrite andb_true_iff; 
      split; [split; [rewrite beq_nat_true_iff|apply beq_ord_refl]|
        apply beq_ord_refl]; trivial.

    right; repeat rewrite orb_true_iff; right.
    repeat rewrite andb_true_iff; split; [split; 
      [apply beq_ord_refl|rewrite beq_nat_true_iff]|]; trivial.

   left; left; repeat rewrite orb_true_iff.
   left; right; rewrite andb_true_iff.
   split; [apply beq_ord_refl|rewrite ltb_iff]; trivial.
Qed.

Lemma btb_beb_iff : forall o o' b,
  btb_ord o o' = b <-> beb_ord o' o = negb b.
unfold beb_ord.
induction o as [n|n p Hp q Hq];
  destruct o' as [n'|n' p' q']; simpl in *; intro b.
 rewrite ltb_leb_iff.
 rewrite leb_ltb_beq_conv.
 rewrite beq_nat_sym; reflexivity.

 destruct b; simpl; split; [discriminate|discriminate|trivial|trivial].

 destruct b; simpl; split; [trivial|trivial|discriminate|discriminate].

 case_eq (btb_ord p p'); intro Hbt; simpl.
  rewrite Hp in Hbt; simpl in Hbt.
  rewrite orb_false_iff in Hbt.
  destruct Hbt as (Hbt1, Hbt2).
  rewrite Hbt1, Hbt2; simpl.
  rewrite andb_false_r; simpl.
  split; intro H; [subst b|]; simpl; trivial.
   destruct b; simpl in H |- *; [trivial|discriminate].

  rewrite Hp in Hbt; simpl in Hbt; simpl.
  rewrite orb_true_iff in Hbt.
  destruct Hbt as [Hbt|Hbt]; repeat rewrite Hbt; simpl.
   case_eq (beq_ord p p'); intro H; [rewrite beq_ord_eq in H; 
     subst p'; rewrite btb_antirefl in Hbt; discriminate|clear H; simpl].
    split; intro H; [subst b|]; simpl; trivial.
     destruct b; simpl in H |- *; [discriminate|trivial].

   rewrite beq_ord_eq in Hbt; subst p'.
   rewrite beq_ord_refl; rewrite btb_antirefl; simpl.
   rewrite andb_true_r.
   case_eq (ltb n' n); intro Hltn; simpl.
    rewrite ltb_leb_iff in Hltn.
    rewrite leb_ltb_beq_conv in Hltn; simpl in Hltn.
    rewrite orb_false_iff in Hltn.
    destruct Hltn as (Hltn, Heqn).
    rewrite beq_nat_sym in Heqn.
    rewrite Hltn; repeat rewrite Heqn; simpl.
    split; intro H; [subst b|]; simpl; trivial.
     destruct b; simpl in H |- *; [trivial|discriminate].

    rewrite ltb_leb_iff in Hltn.
    rewrite leb_ltb_beq_conv in Hltn; simpl in Hltn.
    rewrite orb_true_iff in Hltn.
    destruct Hltn as [Hltn|Heqn].
     rewrite Hltn; apply ltb_leb_iff in Hltn.
     rewrite leb_ltb_beq_conv in Hltn; simpl in Hltn.
     rewrite orb_false_iff in Hltn.
     destruct Hltn as (Hltn, Heqn).
     repeat rewrite Heqn; simpl.
     rewrite beq_nat_sym in Heqn; rewrite Heqn; simpl.
     split; intro H; [subst b|]; simpl; trivial.
      destruct b; simpl in H |- *; [discriminate|trivial].

     rewrite beq_nat_true_iff in Heqn; subst n'.
     rewrite <- (beq_nat_refl n).
     rewrite ltb_antirefl; simpl; apply Hq.
Qed.
    
(*****************************************************************)
(*Max of two ordinals*)
Definition max_ord o o' := if (btb_ord o o') then o else o'.

Lemma btb_max_ord : forall p q r, 
  btb_ord r p = true ->
  btb_ord r q = true ->
  btb_ord r (max_ord p q) = true.
intros p q r; unfold max_ord; case (btb_ord p q); trivial.
Qed.

(*****************************************************************)
(*Cantor Normal Form (CNF) and some properties.*)
Fixpoint CNF (o : Ord) : bool :=
  match o with
    | fin _ => true
    | inf n p Q => ((ltb 0 n)) && (CNF p) && 
      (CNF Q) && (btb_ord p (degree Q))
  end.

Lemma btb_ord_subterm : forall n p q,
  CNF (inf n p q) = true ->
  btb_ord (inf n p q) q = true.
destruct q; intros; simpl in *; trivial.
 repeat rewrite orb_true_iff; left; left.
 rewrite andb_true_iff in H; destruct H as (_, H); trivial.
Qed.

(*Plus and minus operations act as expected only when the *)
(*operands are in CNF*)

Fixpoint ord_plus (o o' : Ord) :=
  match o with
    | fin m  =>
      match o' with
        | fin n => fin (m+n)
        | inf _ _ _ => o'
      end
    | inf n p Q => 
      match o' with
        | fin _ => inf n p (ord_plus Q o')
        | inf n' p' Q' =>
          if (btb_ord p p') then (inf n p (ord_plus Q o')) else 
            if (beq_ord p p') then (inf (n+n') p' Q') else o'
      end
  end.

Lemma degree_plus : forall o o',
  degree (ord_plus o o') = max_ord (degree o) (degree o').
unfold max_ord; destruct o as [|n p Q]; 
  destruct o' as [|n' p' Q']; [simpl|destruct p'; simpl| 
    simpl ord_plus; simpl degree; destruct p as [n'|n' p' Q'];
      [destruct n'|]; simpl|simpl ord_plus]; trivial.
 case_eq (btb_ord p p'); intros Hbt; simpl;
   rewrite Hbt; trivial.
  case_eq (beq_ord p p'); intro Heq; simpl; trivial.
Qed.

Lemma beb_degree_cases : forall (o : Ord),
  match o with
    | fin 0 => beq_ord o (degree o) = true
    | _  => btb_ord o (degree o) = true
  end.
induction o as [n|n p Hp q _].
 destruct n as [|n]; simpl; trivial.

 destruct p as [pn|pn pp pq]; [simpl|]; trivial.
  simpl in Hp |- *; repeat rewrite orb_true_iff; 
    left; left; trivial.
Qed.
 
Lemma beb_degree : forall (o : Ord), 
  beb_ord o (degree o) = true.
intro o; unfold beb_ord; rewrite orb_true_iff.
generalize (beb_degree_cases o); intro H.
destruct o; [destruct n|]; [right|left|left]; trivial.
Qed.

Lemma CNF_ord_plus : forall o o',
  CNF o = true ->
  CNF o' = true ->
  CNF (ord_plus o o') = true.
induction o as [n|n p _ q Hq]; destruct o' as [n'|n' p' q'];
  intros Ho Ho'; simpl in *; trivial;
    repeat rewrite andb_true_iff in Ho;
      destruct Ho as (((Hlt, HCp), HCq), Hdg).
 rewrite degree_plus.
 rewrite Hlt, HCp; simpl.
 rewrite andb_true_iff; split; [apply Hq|]; trivial.
  apply btb_max_ord; simpl; [|apply btb_0 in Hdg]; trivial.

 case_eq (btb_ord p p'); intro Hbtp; simpl.
  rewrite Hlt, HCp; simpl.
  rewrite andb_true_iff; split; [apply Hq; simpl|]; trivial.
   rewrite degree_plus; rewrite btb_max_ord; simpl; trivial.

  case_eq (beq_ord p p'); intro Heqp; simpl; trivial.
   repeat rewrite andb_true_iff in Ho'.
   destruct Ho' as (((Hlt', HCp'), HCq'), Hdg').
   rewrite HCq', HCp', Hdg'; repeat rewrite andb_true_r.
   rewrite ltb_iff in Hlt' |- *.
   apply lt_le_trans with (1:=Hlt') (2:=le_plus_r n n').
Qed.


Lemma ord_plus_0_l : forall (o o' : Ord),
  ZeroO o = true ->
  ord_plus o o' = o'.
destruct o as [n|n p q]; simpl; intros; [|discriminate].
 destruct n as [|n]; intros; [simpl|discriminate].
  destruct o'; trivial.
Qed.

Lemma ord_plus_0_r : forall (o o' : Ord),
  ZeroO o = true ->
  ord_plus o' o = o'.
intro o; destruct o as [n|n p q]; simpl; intros o' H; [|discriminate].
 destruct n; [clear H|discriminate].
  induction o' as [n|n p _ q Hq]; simpl; [
    rewrite plus_0_r |  rewrite Hq]; trivial.
Qed.


Lemma plus_m_r : forall o o' oo, 
  CNF oo = true ->
  btb_ord o o' = true ->
  btb_ord (ord_plus o oo) o' = true.
induction o as [n|n p _ q Hq]; destruct o' as [n'|n' p' q'];
  destruct oo as [nn|nn pp qq]; simpl; intros HCNF H;
    try discriminate; trivial.
 rewrite ltb_iff in H |- *.
 apply lt_plus_trans; trivial.
 
 case (beq_ord p pp); case (btb_ord p pp); simpl; trivial.

 repeat rewrite orb_true_iff in H |- *.
 destruct H as [[H|H]|H]; [left;left|left;right|right]; trivial.
  repeat rewrite andb_true_iff in H |- *.
  destruct H as ((Heqp, Heqn), Hbtq).
  split; [split|apply Hq]; trivial.

 case_eq (btb_ord p pp); intros Hbtppp; simpl.
  repeat rewrite orb_true_iff in H |- *.
  destruct H as [[H|H]|H]; [left;left|left;right|right];trivial.
   repeat rewrite andb_true_iff in H |- *.
   destruct H as ((Heqp, Heqn), Hbtq).
   split; [split|apply Hq]; trivial.

  rewrite btb_beb_iff in Hbtppp; simpl.
  unfold beb_ord in Hbtppp; rewrite orb_true_iff in Hbtppp;
    destruct Hbtppp as [Hbtp|Heqp].
   case_eq (beq_ord p pp); intro Heqp; [rewrite beq_ord_eq in Heqp; 
     subst pp; rewrite btb_antirefl in Hbtp; discriminate|clear Heqp].
    simpl; repeat rewrite orb_true_iff in H |- *; left; left.
    destruct H as [[H|H]|H].
     apply btb_ord_trans with (1:=Hbtp) (2:=H).

     rewrite andb_true_iff in H; destruct H as (H, _).
     rewrite beq_ord_eq in H; subst p'; trivial.

     repeat rewrite andb_true_iff in H; destruct H as ((H, _), _).
     rewrite beq_ord_eq in H; subst p'; trivial.

   rewrite beq_ord_eq in Heqp; subst pp.
   rewrite beq_ord_refl; simpl.
   repeat rewrite andb_true_iff in HCNF;
     destruct HCNF as (((H0n, _), _), _).
   case_eq (btb_ord p p'); intros Hbtp;
    rewrite Hbtp in H; simpl in H |- *; trivial.
    case_eq (beq_ord p p'); intro Heqp;
      rewrite Heqp in H; simpl in H |- *; [|discriminate].
     rewrite orb_true_iff in H |- *.
     destruct H as [H|H]; left; rewrite ltb_iff in H0n |- *.
      rewrite ltb_iff in H; apply lt_plus_trans; trivial.

      rewrite andb_true_iff in H; destruct H as (H, _);
        rewrite beq_nat_true_iff in H; subst n'.
      apply plus_lt_compat_l with (p:=n) in H0n;
        rewrite plus_0_r in H0n; trivial.
Qed.





(*******************************************************************)
(*Pred and Minus*)
Fixpoint ord_pred (o : Ord) : Ord :=
  match o with
    | fin 0 => o
    | fin (S n) => fin n
    | inf n p o' => inf n p (ord_pred o')
  end.

Lemma degree_pred : forall o, degree o = degree (ord_pred o).
destruct o as [n|n p q]; [destruct n|]; simpl; trivial.
Qed.

Lemma CNF_ord_pred : forall o,
  CNF o = true ->
  CNF (ord_pred o) = true.
induction o as [n|n p _ q Hq]; intros Ho; simpl in *; trivial.
 destruct n; simpl; trivial.

 rewrite <- degree_pred.
 repeat rewrite andb_true_iff in Ho.
 destruct Ho as (((Hlt, HCp), HCq), Hdg).
 rewrite Hlt, HCp, Hdg; simpl.
 rewrite andb_true_r.
 apply Hq; trivial.
Qed.

Lemma btb_pred_S : forall o, 
  SuccO o = true ->
  btb_ord o (ord_pred o) = true.
unfold SuccO.
induction o as [n|n p _ q Hq]; intros; simpl in *.
 destruct n; simpl in *; [discriminate|
   rewrite ltb_iff; apply lt_n_Sn].

 rewrite orb_false_r in H.
 rewrite orb_true_iff; right.
 repeat rewrite andb_true_iff.
 split; [split; [rewrite beq_ord_eq|rewrite beq_nat_true_iff]|
   apply Hq; clear n p Hq]; trivial.
  rewrite orb_true_iff.
  destruct q; simpl in *; [right|left]; trivial.
Qed.

Lemma eq_pred_notS : forall o,
  SuccO o = false -> ord_pred o = o.
intro o; unfold SuccO; rewrite orb_false_iff.
induction o as [n|n p _ q Hq]; intro HNS; 
  destruct HNS as (HNS1, HNS2).
 destruct n; simpl in *; [trivial|discriminate].

 simpl in *; rewrite Hq; trivial.
 destruct q as [n'|n' p' q']; [destruct n'|]; 
   simpl in *; [split; trivial|discriminate|split; trivial].
Qed.
 

Fixpoint ord_minus (o o' : Ord) :=
  match o, o' with
    | fin n, fin m => fin (n - m)
    | fin n, inf _ _ _ => o
    | inf n p q, fin _ => inf n p (ord_minus q o')
    | inf n p q, inf n' p' q' =>
      if (btb_ord p p') then inf n p (ord_minus q o') else
        if (beq_ord p p') then 
          (if (ltb n' n) then inf (n-n') p (ord_minus q q') else
            ord_minus q q') 
          else o 
  end.

Lemma ord_minus_degree : forall o o',
  CNF o = true ->
  beb_ord (degree o) (degree (ord_minus o o')) = true.
induction o as [n|n p _ q Hq]; destruct o' as [n'|n' p' q'];
  intro Ho; simpl; trivial.
 unfold beb_ord; rewrite beq_ord_refl;
   rewrite orb_true_r; trivial.

 case_eq (btb_ord p p'); intro Hbtp; simpl;
   [unfold beb_ord; rewrite beq_ord_refl;
     rewrite orb_true_r; trivial|].
  case_eq (beq_ord p p'); intro Heqp; simpl;
    [|unfold beb_ord; rewrite beq_ord_refl;
      rewrite orb_true_r; trivial].
   case_eq (ltb n' n); intro Hltn; simpl;
     [unfold beb_ord; rewrite beq_ord_refl;
       rewrite orb_true_r; trivial|].
    simpl in Ho; repeat rewrite andb_true_iff in Ho;
      destruct Ho as (((_, _), HCq), Hdg).
    specialize Hq with (o':=q') (1:=HCq).
    apply beb_trans with (2:=Hq).
    unfold beb_ord; rewrite Hdg; simpl; trivial.
Qed.


Lemma CNF_ord_minus : forall o o',
  CNF o = true ->
  CNF o' = true ->
  CNF (ord_minus o o') = true.
induction o as [n|n p _ q Hq]; destruct o' as [n'|n' p' q'];
  intros Ho Ho'; simpl in *; trivial;
    repeat rewrite andb_true_iff in Ho;
      destruct Ho as (((Hlt, HCp), HCq), Hdg).
 rewrite Hlt, HCp; simpl.
 rewrite andb_true_iff; split; [apply Hq|]; trivial.
  apply btb_beb_trans with (1:=Hdg).
  apply ord_minus_degree; trivial.

 case_eq (btb_ord p p'); intro Hbtp; simpl.
  rewrite Hlt, HCp; simpl.
  rewrite andb_true_iff; split; [apply Hq; simpl|]; trivial.
   apply btb_beb_trans with (1:=Hdg).
   apply ord_minus_degree; trivial.

  case_eq (beq_ord p p'); intro Heqp; simpl;
    [|repeat rewrite andb_true_iff; repeat split; trivial].
   repeat rewrite andb_true_iff in Ho'.
   destruct Ho' as (((Hlt', HCp'), HCq'), Hdg').
   case_eq (ltb n' n); intro Hltn; simpl; [|apply Hq; trivial].
    rewrite HCp; rewrite andb_true_r.
    repeat rewrite andb_true_iff; 
      repeat split; [|apply Hq; trivial|].
     rewrite ltb_iff in Hltn |- *.
     unfold lt in Hltn |- *.
     apply minus_le_compat_r with (p:=n') in Hltn.
     rewrite <- minus_Sn_m in Hltn; trivial.
     rewrite minus_diag in Hltn; trivial.

     apply btb_beb_trans with (1:=Hdg).
     apply ord_minus_degree; trivial.
Qed.


Lemma btb_minus : forall o' o oo,
  CNF o' = true ->
  CNF o  = true ->
  CNF oo = true ->
  btb_ord o o' = true -> 
  btb_ord o (ord_minus o' oo) = true.
induction o' as [n'|n' p' _ q' Hq'].
 destruct o as [n|n p q]; [|destruct oo; simpl; trivial].
  destruct oo as [nn|nn pp qq]; simpl; trivial.
   do 2 rewrite ltb_iff; intros _ _ _ H.
   apply le_lt_trans with (1:=le_minus n' nn) (2:=H).

 destruct o as [n|n p q]; [simpl; discriminate|intros oo Ho' Ho Hoo H].
  destruct oo as [nn|nn pp qq]; [
    simpl; repeat rewrite orb_true_iff|simpl ord_minus].
   simpl in H; repeat rewrite orb_true_iff in H.
   destruct H as [[H|H]|H]; [left;left|left;right|right]; trivial.
    repeat rewrite andb_true_iff in H |- *.
    destruct H as ((Hpp, Hnn), Hqq).
    simpl in Ho, Ho'; repeat rewrite andb_true_iff in Ho, Ho'.
    destruct Ho as (((_, _), Ho), _).
    destruct Ho' as (((_, _), Ho'), _).
    split; [split|apply Hq'; simpl]; trivial.     

   case_eq (btb_ord p' pp); intros _ ; [simpl|].
    repeat rewrite orb_true_iff.
    simpl in H; repeat rewrite orb_true_iff in H.
    destruct H as [[H|H]|H]; [left;left|left;right|right]; trivial.
     repeat rewrite andb_true_iff in H |- *.
     destruct H as ((Hpp, Hnn), Hqq).
      simpl in Ho, Ho'; repeat rewrite andb_true_iff in Ho, Ho'.
      destruct Ho as (((_, _), Ho), _).
      destruct Ho' as (((_, _), Ho'), _).
      split; [split|apply Hq'; simpl]; trivial.
       
    case_eq (beq_ord p' pp); intro Hppp; [
      rewrite beq_ord_eq in Hppp; subst pp|trivial].
     case_eq (ltb nn n'); intros Hnn ; [simpl|].
      repeat rewrite orb_true_iff.
      simpl in Hoo; repeat rewrite andb_true_iff in Hoo; 
        destruct Hoo as (((Hoo, _), _), _).
      simpl in H; repeat rewrite orb_true_iff in H.
      destruct H as [[H|H]|H]; [left;left| |]; trivial; left; right; 
        repeat rewrite andb_true_iff in H |- *. 
       destruct H as (Heqp, Hn).
       split; [trivial|].
        rewrite ltb_iff in Hn, Hnn, Hoo |- *.
        apply lt_trans with (2:=Hn).
        apply lt_minus; [apply lt_le_weak|]; trivial.
        
       rewrite andb_true_iff in H. 
       destruct H as ((Heqp, Hn), _).
       split; [trivial|].
        rewrite beq_nat_true_iff in Hn; subst n'.
        rewrite ltb_iff in Hnn, Hoo |- *.
        apply lt_minus; [apply lt_le_weak|]; trivial.
      
      apply btb_ord_trans with (o2:=(inf n' p' q')); trivial.
       generalize Ho'; intro H'.
       simpl in Ho, Ho', Hoo.
       repeat rewrite andb_true_iff in Ho, Ho', Hoo.
       destruct Ho as (((_, _), Ho), _).
       destruct Ho' as (((_, _), Ho'), _).
       destruct Hoo as (((_, _), Hoo), _).
        apply Hq'; [| | |apply btb_ord_subterm]; trivial.
Qed.


Lemma plus_bt_minus : forall o o' oo, 
  CNF o  = true ->
  CNF o' = true ->
  CNF oo = true ->
  btb_ord o oo = false ->
  btb_ord (ord_plus o o') oo = true -> 
  btb_ord o' (ord_minus oo o) = true.
induction o as [n|n p _ q Hq]; destruct oo as [nn|nn pp qq]; 
  destruct o' as [n'|n' p' q']; intros Ho Ho' Hoo H H';
    try discriminate; trivial.
 simpl in H, H' |- *.
 rewrite ltb_leb_iff in H; simpl in H; rewrite leb_iff in H.
 rewrite ltb_iff in H' |- *; unfold lt in H' |- *.
 apply minus_le_compat_r with (p:=n) in H'.
 rewrite minus_plus in H'.
 rewrite <- minus_Sn_m in H'; trivial.
 
 simpl ord_plus in H'.
 apply btb_minus; trivial.


 simpl in Ho, Hoo.
 repeat rewrite andb_true_iff in Ho, Hoo.
 destruct Ho as (((_, _), Ho), _).
 destruct Hoo as (((_, _), Hoo), _).
 simpl in H', H; simpl ord_minus.
 repeat rewrite orb_false_iff in H.
 destruct H as ((Hbt1, Hbt2), Hbt3).
 rewrite Hbt1, Hbt2 in H'; simpl in H'.
 rewrite btb_beb_iff in Hbt1; 
   unfold beb_ord in Hbt1; simpl in Hbt1.
 rewrite orb_true_iff in Hbt1; destruct Hbt1 as [Hbt|Heq].
  rewrite Hbt; rewrite btb_beb_iff in Hbt; simpl in Hbt.
  unfold beb_ord in Hbt; rewrite orb_false_iff in Hbt.
  destruct Hbt as (Hbt, Heq).
  rewrite Heq in H'; simpl in H'; discriminate.
  
  rewrite beq_ord_eq in Heq; subst pp; rewrite btb_antirefl.
  rewrite beq_ord_refl in Hbt2, Hbt3, H' |- *; 
    simpl in Hbt2, Hbt3, H'.
  rewrite ltb_leb_iff in Hbt2.
  rewrite leb_ltb_beq_conv in Hbt2; simpl in Hbt2.
  rewrite orb_true_iff in Hbt2; destruct Hbt2 as [Hlt|Heq].
   rewrite Hlt; rewrite ltb_leb_iff in Hlt.
   rewrite leb_ltb_beq_conv in Hlt; simpl in Hlt.
   rewrite orb_false_iff in Hlt; destruct Hlt as (_, Heq).
   rewrite beq_nat_sym in Heq; rewrite Heq in H'; 
     simpl in H'; discriminate.

   rewrite Heq in Hbt3, H'; simpl in Hbt3, H'.
   rewrite beq_nat_true_iff in Heq; subst nn.
   rewrite ltb_antirefl; apply Hq; trivial.
   
 simpl ord_plus in H'.
 case_eq (btb_ord p p'); intros Hbtp; rewrite Hbtp in H'.
  simpl in H, H'; simpl ord_minus.
  case_eq (btb_ord p pp); intros Hbtppp; 
    rewrite Hbtppp in H; simpl in H; [discriminate|].
   rewrite btb_beb_iff in Hbtppp; simpl in Hbtppp.
   unfold beb_ord in Hbtppp; rewrite orb_true_iff in Hbtppp.
   destruct Hbtppp as [Hppp|Hppp].
    rewrite btb_beb_iff in Hppp; simpl in Hppp.
    unfold beb_ord in Hppp; rewrite orb_false_iff in Hppp.
    destruct Hppp as (Hbtpp, Heqp); rewrite Hbtpp, Heqp in H'; 
      simpl in H'; discriminate.

    rewrite beq_ord_eq in Hppp; subst pp.
    rewrite btb_antirefl in H' |- *.
    repeat rewrite beq_ord_refl in H, H'; simpl in H, H'.
    case_eq (ltb nn n); intro Hnnn; 
      rewrite Hnnn in H, H'; simpl in H, H'; [discriminate|].
     rewrite ltb_leb_iff in Hnnn; simpl in Hnnn.
     rewrite leb_ltb_beq_conv in Hnnn; 
       rewrite orb_true_iff in Hnnn; destruct Hnnn as [Hnnn|Hnnn].
      rewrite ltb_leb_iff in Hnnn; simpl in Hnnn.
      rewrite leb_ltb_beq_conv in Hnnn; rewrite orb_false_iff in Hnnn;
        destruct Hnnn as (_, Hnnn); rewrite beq_nat_sym in Hnnn;
          rewrite Hnnn in H'; simpl in H'; discriminate.

      rewrite Hnnn in H, H'; simpl in H, H'.
      rewrite beq_nat_true_iff in Hnnn; subst nn.
      rewrite ltb_antirefl, beq_ord_refl.
      simpl in Ho, Hoo.
      repeat rewrite andb_true_iff in Ho, Hoo.
      destruct Ho as (((_, _), Ho), _).
      destruct Hoo as (((_, _), Hoo), _).
      apply Hq; trivial.

  rewrite btb_beb_iff in Hbtp; simpl in Hbtp.
  unfold beb_ord in Hbtp; rewrite orb_true_iff in Hbtp.
  destruct Hbtp as [Hpp'|Hpp'].
   rewrite btb_beb_iff in Hpp'; simpl in Hpp';
     unfold beb_ord in Hpp'; rewrite orb_false_iff in Hpp'.
   destruct Hpp' as (_, Hpp'); rewrite Hpp' in H'.
   apply btb_minus; trivial.

  rewrite beq_ord_eq in Hpp'; subst p'.
  rewrite beq_ord_refl in H'.
  case_eq (btb_ord p pp); intros Hbt; [
    simpl in H; rewrite Hbt in H; simpl in H; discriminate|].
   rewrite btb_beb_iff in Hbt; simpl in Hbt.
   unfold beb_ord in Hbt; rewrite orb_true_iff in Hbt.
   destruct Hbt as [Hbt|Heq]; [
     simpl in H'; rewrite btb_beb_iff in Hbt; simpl in Hbt;
       unfold beb_ord in Hbt; rewrite orb_false_iff in Hbt;
         destruct Hbt as (Hbt, Heq); rewrite Hbt, Heq in H';
           simpl in H'; discriminate|].
    rewrite beq_ord_eq in Heq; subst pp.
    case_eq (ltb nn n); intros Heqn; simpl in H.
     rewrite btb_antirefl in H; repeat rewrite beq_ord_refl in H;
       rewrite Heqn in H; simpl in H; discriminate.
     
     simpl in H'; simpl ord_minus.
     simpl in Ho, Hoo.
     repeat rewrite andb_true_iff in Ho, Hoo.
     destruct Ho as (((_, _), Ho), _).
     destruct Hoo as (((_, _), Hoo), Hdegree).
     rewrite btb_antirefl in H, H' |- *; simpl in H, H'.
     repeat rewrite beq_ord_refl in H, H'; simpl in H, H'.
     rewrite beq_ord_refl.
     rewrite Heqn in H; simpl in H, H'.
     rewrite ltb_leb_iff in Heqn; simpl in Heqn.
     rewrite leb_ltb_beq_conv in Heqn; rewrite orb_true_iff in Heqn.
     destruct Heqn as [Hlt|Heq].
      rewrite Hlt; simpl; rewrite btb_antirefl; 
        repeat rewrite beq_ord_refl; simpl; rewrite orb_true_iff.
      case_eq (ltb nn (n+n')); intros Heqn; 
        rewrite Heqn in H'; simpl in H' |- *; [left|right].
       rewrite ltb_iff in Hlt, Heqn |- *.
       apply lt_le_weak in Hlt; unfold lt in Heqn |- *.
       apply minus_le_compat_r with (p:=n) in Heqn.
       rewrite minus_plus in Heqn.
       rewrite <- minus_Sn_m in Heqn; trivial.

       rewrite ltb_leb_iff in Heqn; unfold beb_ord in Heqn;
         simpl in Heqn; rewrite leb_ltb_beq_conv in Heqn;
           rewrite orb_true_iff in Heqn; destruct Heqn as [Hltn|Heqn].
        rewrite ltb_leb_iff in Hltn; unfold beb_ord in Hltn;
          simpl in Hltn; rewrite leb_ltb_beq_conv in Hltn;
            rewrite orb_false_iff in Hltn; destruct Hltn as (Hltn,Heqn).
        rewrite beq_nat_sym in Heqn; rewrite Heqn in H'; 
          simpl in H'; discriminate.

        rewrite Heqn in H'; simpl in H'.
        rewrite beq_nat_true_iff in Heqn; subst nn.
        rewrite minus_plus; rewrite <- (beq_nat_refl n'); simpl.
        simpl in Ho'; repeat rewrite andb_true_iff in Ho'.
        destruct Ho' as (((_, _), Ho'), _).
        apply btb_minus; trivial.
        
      rewrite beq_nat_true_iff in Heq; subst nn.
      rewrite ltb_antirefl.
      rewrite <- (beq_nat_refl n) in H; simpl in H.
      apply btb_minus; trivial.
       destruct qq; simpl; 
         [|simpl in Hdegree; rewrite Hdegree; simpl]; trivial.
Qed.
  

(******************************************************************)
(*Cantor Normal Form Ordinals*)
(******************************************************************)
Definition CNFO := {o : Ord | CNF o = true}.

Definition CNFO_plus (o : CNFO) (o' : CNFO) : CNFO.
destruct o as (o, CNFo); destruct o' as (o', CNFo').
exists (ord_plus o o').
apply CNF_ord_plus; trivial.
Defined.

Definition CNFO_pred (o : CNFO) : CNFO.
destruct o as (o, CNFO).
exists (ord_pred o).
apply CNF_ord_pred; trivial.
Defined.

Definition CNFO_minus (o : CNFO) (o' : CNFO) : CNFO.
destruct o as (o, CNFo); destruct o' as (o', CNFo').
exists (ord_minus o o').
apply CNF_ord_minus; trivial.
Defined.

Definition CNFO_nat (n : nat) : CNFO.
exists (fin n); simpl; trivial.
Defined.

Definition CNFO_btb (o o' : CNFO) := 
  btb_ord (proj1_sig o) (proj1_sig o').

Definition CNFO_beq (o o' : CNFO) := 
  beq_ord (proj1_sig o) (proj1_sig o').


(******************************************************************)
(*A path with an ordinal length*)
(******************************************************************)

Section Path.
 
 Variable A : Type.
 Variable eq_A : A -> A -> bool.

 Definition domain (o : CNFO) := {i: CNFO|CNFO_btb o i = true}.

 Definition path (o : CNFO) := (domain o) -> A.

 Definition join (o o' : CNFO) (p : path o) (p' : path o') : 
   option (path (CNFO_plus (CNFO_pred o) o')).
 case_eq (ZeroO (proj1_sig o')); intros HO; [exact None|].
  (*The second path is not length 0*)
  case_eq (SuccO (proj1_sig o)); intro HS.
   (*The first path is of length (w^pi*ci + S n) *)
   assert (domain o) as po. (*The last index of fst path*)
    exists (CNFO_pred o).
    destruct o, o'; simpl in HS |- *.
    unfold CNFO_btb; apply btb_pred_S in HS; trivial.
   assert (domain o') as po'. (*The first index of snd path*)
    exists (CNFO_nat 0).
    destruct o'; unfold CNFO_btb; simpl.
    apply not_0_bt_0; trivial.
   case_eq (eq_A (p po) (p' po')); intro Heq; [|exact None].
    (*The last el of fst path is equal to the fst el of snd path*)
    assert (f : path (CNFO_plus (CNFO_pred o) o')).
     intros oo; destruct oo as (oo, Hoo).
     case_eq (btb_ord (ord_pred (proj1_sig o)) (proj1_sig oo)); 
     intros Hpart.
      (*The index oo < o - 1*)
      assert (domain o) as poo.
       exists oo.
       apply btb_ord_trans with (2:=Hpart).
       apply btb_pred_S; trivial.
      exact (p poo).
      (*The index oo >= o - 1*)
      assert (domain o') as poo.
       exists (CNFO_minus oo (CNFO_pred o)).
       unfold CNFO_btb in Hoo |- *.
       destruct o as (o, cnfo); destruct o' as (o', cnfo');
         destruct oo as (oo, cnfoo); simpl in Hoo, Hpart |- *.
       apply plus_bt_minus; trivial.
        apply CNF_ord_pred; trivial.
      exact (p' poo).
    exact (Some f).
    
   (*The length of fst path is not succ case*)
   assert (f : path (CNFO_plus (CNFO_pred o) o')).
    intros oo; destruct oo as (oo, Hoo).
    case_eq (CNFO_btb o oo); intros Hpart.
      (*The index oo < o*)
      assert (domain o) as poo.
       exists oo; trivial.
      exact (p poo).
      (*The index oo >= o*)
      assert (domain o') as poo.
       exists (CNFO_minus oo o).
       unfold CNFO_btb in Hoo, Hpart |- *.
       destruct o as (o, cnfo); destruct o' as (o', cnfo');
         destruct oo as (oo, cnfoo); simpl in Hoo, Hpart, HS |- *.
        rewrite eq_pred_notS in Hoo; trivial.
        apply plus_bt_minus; trivial.
      exact (p' poo).
    exact (Some f).
 Defined.

End Path.



(******************************************************************)
(*Set of paths*)
(******************************************************************)

Set Implicit Arguments.

Section SetOfPaths.

 Parameter A : Type.
 Parameter eq_A : A -> A -> bool.
 
 Definition PathSet (o : CNFO) := path A o -> Prop.

 Definition pathin o (s : PathSet o) (p : path A o) := s p.

 Inductive setjoin o o' (s : PathSet o) (s' : PathSet o') : 
   PathSet (CNFO_plus (CNFO_pred o) o') :=
   jointwo : forall p p' p'', 
     pathin s p ->
     pathin s' p' ->
     join A eq_A o o' p p' = Some p'' ->
     pathin (setjoin s s') p''.

 Definition set_include o o' (s : PathSet o) (s' : PathSet o') :=
   CNFO_beq o o' /\ 
 
  
 

 Lemma setjoin_comm : forall or os oq 
   (r : PathSet or) (s : PathSet os) (q : PathSet oq),
   setjoin (setjoin r s) q 







 (*Don't requrie elements are different, infinitely many elements*)
(* Record PathSet := mkset {
   elelen : CNFO -> CNFO;
   elemen : forall (o : CNFO), path A (elelen o)
 }.

 Definition constone : CNFO.
 exists (fin 1); trivial.
 Defined.

 Definition one : PathSet.
 exists (fun _ => constone).
 intro index.
 unfold path.
 *)

 
  



