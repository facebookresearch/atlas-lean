/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Finite.Sigma
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.Ring

/-!
# Counting signed inversion sequences by the first bar

We prove the Wilf-equivalence and common counting formula of Mansour and Safadi's
Lemma 4 by counting the possible suffixes after the first barred entry.
-/

namespace MetaMathlibExt

open Nat

namespace signedInvSeq_wilf_and_count_b0b1_b0b0_b01

private abbrev Entry := ℕ × Bool

private abbrev patterns (equalBar : Bool) : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.eq, true, !equalBar⟩, ⟨.lt, true, false⟩}

-- After a barred entry, only smaller magnitudes and one sign at equality are allowed.
private def Allowed (equalBar : Bool) (x y : Entry) : Prop :=
  x.2 = true → y.1 ≤ x.1 ∧ (y.1 = x.1 → y.2 = equalBar)

private def Avoids (equalBar : Bool) {n : ℕ} (e : Fin n → Entry) : Prop :=
  ∀ i j, i < j → Allowed equalBar (e i) (e j)

private theorem avoids_iff (s : Bool) {n : ℕ} (e : Fin n → Entry) :
    (∀ p ∈ patterns s, ¬ SignedInvSeqContains e p) ↔ Avoids s e := by
  have cmp_lt (a b : ℕ) : (Ordering.lt = compare a b) ↔ a < b :=
    eq_comm.trans compare_lt_iff_lt
  have cmp_eq (a b : ℕ) : (Ordering.eq = compare a b) ↔ a = b :=
    eq_comm.trans compare_eq_iff_eq
  have pair (i j : Fin n) :
      ⟨compare (e i).1 (e j).1, (e i).2, (e j).2⟩ ∉ patterns s ↔
        Allowed s (e i) (e j) := by
    cases s <;> cases hi : (e i).2 <;> cases hj : (e j).2 <;>
      simp [patterns, Allowed, hi, hj, SignedPattern2.mk.injEq, cmp_lt, cmp_eq,
        not_lt, eq_comm, and_comm]
  constructor
  · intro h i j hij
    exact (pair i j).mp fun hm => h _ hm ⟨i, j, hij, rfl, rfl, rfl⟩
  · rintro h p hm ⟨i, j, hij, ho, hs, ht⟩
    apply (pair i j).mpr (h i j hij)
    simpa only [ho, hs, ht] using hm

private theorem avoids_cons (s : Bool) {n : ℕ} (x : Entry) (e : Fin n → Entry) :
    Avoids s (Fin.cons x e) ↔ Avoids s e ∧ ∀ i, Allowed s x (e i) := by
  constructor
  · intro h
    exact ⟨fun i j hij => by simpa using h i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij),
      fun i => by simpa using h 0 i.succ (Fin.succ_pos i)⟩
  · rintro ⟨h, hx⟩ i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases (by simp) (fun j => ?_) j
      simpa using hx j
    · refine Fin.cases (by simp) (fun j => ?_) j
      simpa using h i j

private abbrev Tail (s : Bool) (m n : ℕ) :=
  {e : Fin n → Entry // Avoids s e ∧ ∀ i, Allowed s (m, true) (e i)}

private abbrev Words (s : Bool) (j n : ℕ) :=
  {e : Fin n → Entry // Avoids s e ∧ ∀ i, (e i).1 ≤ j + i.val}

private theorem finite_of_bound {n : ℕ} {q : (Fin n → Entry) → Prop} (b : Fin n → ℕ)
    (h : ∀ e, q e → ∀ i, (e i).1 ≤ b i) : Finite {e // q e} :=
  Finite.of_injective
    (fun (e : {e // q e}) (i : Fin n) =>
      ((⟨(e.val i).1, Nat.lt_succ_of_le (h e.val e.property i)⟩ : Fin (b i + 1)), (e.val i).2))
    (by
      intro e f hef
      apply Subtype.ext
      funext i
      exact Prod.ext (congrArg (fun a => (a i).1.val) hef) (congrArg (fun a => (a i).2) hef))

private instance tailFinite (s : Bool) (m n : ℕ) : Finite (Tail s m n) :=
  finite_of_bound (fun _ => m) fun _ h i => (h.2 i rfl).1

private instance wordsFinite (s : Bool) (j n : ℕ) : Finite (Words s j n) :=
  finite_of_bound (fun i => j + i.val) fun _ h => h.2

-- Split off the head of a nonempty word, keeping the dependent condition on its tail.
private def consEquiv {n : ℕ} (P : (Fin (n + 1) → Entry) → Prop)
    (Q : Entry → Prop) (R : Entry → (Fin n → Entry) → Prop)
    (h : ∀ x e, P (Fin.cons x e) ↔ Q x ∧ R x e) :
    {e // P e} ≃ Σ x : {x // Q x}, {e // R x.val e} where
  toFun e := by
    have he := (h (e.val 0) (Fin.tail e.val)).mp (by simpa using e.property)
    exact ⟨⟨e.val 0, he.1⟩, ⟨Fin.tail e.val, he.2⟩⟩
  invFun f := ⟨Fin.cons f.1.val f.2.val, (h _ _).mpr ⟨f.1.property, f.2.property⟩⟩
  left_inv e := Subtype.ext (Fin.cons_self_tail e.val)
  right_inv f := by
    rcases f with ⟨⟨x, hx⟩, ⟨e, he⟩⟩
    simp
    rfl

private def nextBound (m : ℕ) (x : Entry) : ℕ := if x.2 then x.1 else m

private theorem allowed_trans (s : Bool) {m : ℕ} {x y : Entry}
    (hx : Allowed s (m, true) x) (hb : x.2 = true)
    (hy : Allowed s x y) : Allowed s (m, true) y := by
  intro _
  have hxm := (hx rfl).1
  have hyx := (hy hb).1
  refine ⟨hyx.trans hxm, fun hym => (hy hb).2 (by omega)⟩

private theorem tail_cons (s : Bool) (m : ℕ) {n : ℕ} (x : Entry) (e : Fin n → Entry) :
    (Avoids s (Fin.cons x e) ∧
      ∀ i, Allowed s (m, true) (Fin.cons (α := fun _ => Entry) x e i)) ↔
      Allowed s (m, true) x ∧ (Avoids s e ∧ ∀ i, Allowed s (nextBound m x, true) (e i)) := by
  rw [avoids_cons, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rcases hb : x.2 with _ | _
  · simp only [nextBound, hb, Bool.false_eq_true, ite_false, Allowed, false_implies, implies_true,
      and_true]
    tauto
  · have he : (x.1, true) = x := Prod.ext rfl hb.symm
    simp only [nextBound, hb, ite_true, he]
    constructor
    · rintro ⟨⟨h, hy⟩, hx, _⟩
      exact ⟨hx, h, hy⟩
    · rintro ⟨hx, h, hy⟩
      exact ⟨⟨h, hy⟩, hx, fun i => allowed_trans s hx hb (hy i)⟩

-- A smaller unbarred entry or the unique entry at equality leaves the bound unchanged.
-- A smaller barred entry changes it to that entry's magnitude.
private def tailHeadEquiv (s : Bool) (m : ℕ) :
    Fin (m + 1) ⊕ Fin m ≃ {x : Entry // Allowed s (m, true) x} where
  toFun := Sum.elim
    (fun i => ⟨(i.val, s && decide (i.val = m)), fun _ =>
      ⟨Nat.le_of_lt_succ i.isLt, fun h => by
        change i.val = m at h
        simp [h]⟩⟩)
    (fun i => ⟨(i.val, true), fun _ => ⟨i.isLt.le, fun h => (i.isLt.ne h).elim⟩⟩)
  invFun x :=
    if h : x.val.2 = true ∧ x.val.1 < m then .inr ⟨x.val.1, h.2⟩
    else .inl ⟨x.val.1, Nat.lt_succ_of_le (x.property rfl).1⟩
  left_inv := by
    intro i
    rcases i with i | i
    · change (if h : (s && decide (i.val = m)) = true ∧ i.val < m
        then Sum.inr ⟨i.val, h.2⟩ else Sum.inl i) = (Sum.inl i : Fin (m + 1) ⊕ Fin m)
      exact dite_eq_right (fun h =>
        (of_decide_eq_true (Bool.and_eq_true_iff.mp h.1).2).not_lt h.2)
    · simp [i.isLt]
  right_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    obtain ⟨ha, hs⟩ := h rfl
    simp only at ha hs
    by_cases hlt : b = true ∧ a < m
    · simp only [dite_eq_left hlt, Sum.elim_inr]
      exact Subtype.ext (Prod.ext rfl hlt.1.symm)
    · simp only [dite_eq_right hlt, Sum.elim_inl]
      apply Subtype.ext
      refine Prod.ext rfl ?_
      change (s && decide (a = m)) = b
      by_cases he : a = m
      · simpa [he] using (hs he).symm
      · have hb : b = false := Bool.eq_false_iff.mpr fun hb =>
          hlt ⟨hb, lt_of_le_of_ne ha he⟩
        simp [he, hb]

private theorem tail_card_succ (s : Bool) (m n : ℕ) :
    Nat.card (Tail s m (n + 1)) =
      (m + 1) * Nat.card (Tail s m n) + ∑ a : Fin m, Nat.card (Tail s a.val n) := by
  let splitHead := consEquiv
    (fun e => Avoids s e ∧ ∀ i, Allowed s (m, true) (e i))
    (Allowed s (m, true))
    (fun x e => Avoids s e ∧ ∀ i, Allowed s (nextBound m x, true) (e i))
    (tail_cons s m (n := n))
  let reindex := splitHead.trans (Equiv.sigmaCongrLeft (tailHeadEquiv s m)).symm
  let splitCases := Equiv.sumSigmaDistrib
    (fun a => Tail s (nextBound m ((tailHeadEquiv s m) a).val) n)
  have left (a : Fin (m + 1)) : nextBound m ((tailHeadEquiv s m) (.inl a)).val = m := by
    by_cases ha : a.val = m <;> simp [nextBound, tailHeadEquiv, ha]
  have right (a : Fin m) : nextBound m ((tailHeadEquiv s m) (.inr a)).val = a.val := by
    simp [nextBound, tailHeadEquiv]
  rw [Nat.card_congr (reindex.trans splitCases), Nat.card_sum, Nat.card_sigma, Nat.card_sigma]
  simp [left, right]

private theorem card_word_zero (q : (Fin 0 → Entry) → Prop) (h : ∀ e, q e) :
    Nat.card {e // q e} = 1 := by
  refine Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨Fin.elim0, h _⟩⟩⟩

private theorem sum_tail_succ (s : Bool) (n m : ℕ) :
    (∑ a : Fin m, Nat.card (Tail s a.val (n + 1))) =
      m * ∑ a : Fin m, Nat.card (Tail s a.val n) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, tail_card_succ]
    ring

private theorem sum_tail (s : Bool) (n m : ℕ) :
    (∑ a : Fin m, Nat.card (Tail s a.val n)) = m ^ (n + 1) := by
  induction n with
  | zero =>
    have hz (a : ℕ) : Nat.card (Tail s a 0) = 1 :=
      card_word_zero _ (fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩)
    simp [hz]
  | succ n ih =>
    rw [sum_tail_succ, ih]
    exact (_root_.pow_succ' m (n + 1)).symm

private def wordTail (s : Bool) (j : ℕ) {n : ℕ} (x : Entry) (e : Fin n → Entry) : Prop :=
  Avoids s e ∧ ∀ i, if x.2 then Allowed s x (e i) else (e i).1 ≤ j + 1 + i.val

private theorem word_cons (s : Bool) (j : ℕ) {n : ℕ} (x : Entry) (e : Fin n → Entry) :
    (Avoids s (Fin.cons x e) ∧ ∀ i : Fin (n + 1), (Fin.cons (α := fun _ => Entry) x e i).1 ≤
      j + i.val) ↔ x.1 ≤ j ∧ wordTail s j x e := by
  rw [avoids_cons, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, add_zero, Fin.val_succ, wordTail]
  rcases hb : x.2 with _ | _
  · simp only [Allowed, hb, Bool.false_eq_true, ite_false, false_implies, implies_true, and_true]
    simp only [Nat.add_assoc, Nat.add_comm 1]
    tauto
  · simp only [ite_true]
    constructor
    · rintro ⟨⟨h, hx⟩, hj, _⟩
      exact ⟨hj, h, hx⟩
    · rintro ⟨hj, h, hx⟩
      exact ⟨⟨h, hx⟩, hj, fun i => ((hx i hb).1.trans hj).trans (Nat.le_add_right _ _)⟩

private def wordHeadEquiv (j : ℕ) :
    Fin (j + 1) ⊕ Fin (j + 1) ≃ {x : Entry // x.1 ≤ j} where
  toFun := Sum.elim (fun i => ⟨(i.val, false), Nat.le_of_lt_succ i.isLt⟩)
    (fun i => ⟨(i.val, true), Nat.le_of_lt_succ i.isLt⟩)
  invFun x := if x.val.2 then .inr ⟨x.val.1, Nat.lt_succ_of_le x.property⟩
    else .inl ⟨x.val.1, Nat.lt_succ_of_le x.property⟩
  left_inv := by rintro (i | i) <;> rfl
  right_inv := by rintro ⟨⟨a, b⟩, h⟩; cases b <;> rfl

-- An unbarred head consumes one position. A barred head bounds the whole remaining word.
private theorem words_card_succ (s : Bool) (j n : ℕ) :
    Nat.card (Words s j (n + 1)) =
      (j + 1) * Nat.card (Words s (j + 1) n) + (j + 1) ^ (n + 1) := by
  let splitHead := consEquiv (fun e => Avoids s e ∧ ∀ i, (e i).1 ≤ j + i.val)
    (fun x => x.1 ≤ j) (wordTail s j) (word_cons s j (n := n))
  let reindex := splitHead.trans (Equiv.sigmaCongrLeft (wordHeadEquiv j)).symm
  let splitCases := Equiv.sumSigmaDistrib
    (fun a => {e : Fin n → Entry // wordTail s j ((wordHeadEquiv j) a).val e})
  let unbarredProduct := Equiv.sumCongr (Equiv.sigmaEquivProd (Fin (j + 1)) (Words s (j + 1) n))
    (Equiv.refl (Σ a : Fin (j + 1), Tail s a.val n))
  rw [Nat.card_congr (reindex.trans (splitCases.trans unbarredProduct)), Nat.card_sum,
    Nat.card_prod, Nat.card_sigma, Nat.card_fin, sum_tail]

private theorem words_card_factorial (s : Bool) (n j : ℕ) :
    j ! * Nat.card (Words s j n) =
      ∑ k ∈ Finset.range (n + 1), (j + k) ! * (j + k + 1) ^ (n - k) := by
  induction n generalizing j with
  | zero =>
    have hz : Nat.card (Words s j 0) = 1 :=
      card_word_zero _ (fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩)
    simp [hz]
  | succ n ih =>
    rw [words_card_succ, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (j !) (j + 1),
      ← Nat.factorial_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show j + 1 + k = j + (k + 1) by omega]

private theorem avoid_count (s : Bool) (n : ℕ) :
    signedInvAvoidCount (patterns s) n = ∑ j ∈ Finset.range (n + 1), j ! * (j + 1) ^ (n - j) := by
  have h : signedInvAvoidCount (patterns s) n = Nat.card (Words s 0 n) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun e => by
      rw [avoids_iff, and_comm]
      simp
  simpa [h] using words_card_factorial s n 0

end signedInvSeq_wilf_and_count_b0b1_b0b0_b01

open signedInvSeq_wilf_and_count_b0b1_b0b0_b01 in
/-- **Mansour–Safadi Lemma 4 (signed patterns 0̄1̄, 0̄0̄, 0̄1).** A signed inversion sequence of
length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1, \dots, k - 1,
\overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$, $01$, $10$,
each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as $|\tau_1|$,
$|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write $\bar I_n(B)$ for the
set of signed inversion sequences of length $n$ that avoid every pattern in $B$. For every
$n \ge 0$, $|\bar I_n(\{\bar 0\bar 1, \bar 0\bar 0, \bar 0 1\})| =
|\bar I_n(\{\bar 0\bar 1, \bar 0 0, \bar 0 1\})| = \sum_{j=0}^{n} j!\,(j + 1)^{n - j}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 4 (`integers-2026-A74-lem-4`). -/
public theorem signedInvSeq_wilf_and_count_b0b1_b0b0_b01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩} ∧
    ∀ n, signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩} n =
        ∑ j ∈ Finset.range (n + 1), j ! * (j + 1) ^ (n - j) := by
  constructor
  · funext n
    exact (avoid_count false n).trans (avoid_count true n).symm
  · exact avoid_count false

end MetaMathlibExt
