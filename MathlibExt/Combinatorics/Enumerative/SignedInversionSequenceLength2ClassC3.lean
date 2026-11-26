/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Logic.Equiv.Sum

/-!
# Signed inversion sequences in class C3

We prove the Wilf-equivalence and factorial-sum count for the three pattern sets in class C3.
For each set, the avoiders with a bar are in bijection with all avoiders one position shorter.
-/

namespace MetaMathlibExt

open Nat

namespace signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1

private abbrev Entry := ℕ × Bool

-- The two suffix classes differ only in the sign allowed after a bar at equal magnitude.
private abbrev suffixPatterns (b : Bool) : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.eq, true, !b⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩}

private abbrev prefixPatterns : Finset SignedPattern2 :=
  {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩}

private def SuffixAllowed (b : Bool) (x y : Entry) : Prop :=
  (x.2 = true ∨ y.2 = true → y.1 ≤ x.1) ∧
    (x.2 = true → x.1 = y.1 → y.2 = b)

private def PrefixAllowed (x y : Entry) : Prop :=
  (x.2 = true ∨ y.2 = true → x.1 ≠ y.1) ∧
    (x.2 = false → y.2 = true → y.1 ≤ x.1)

private def Bounded {n : ℕ} (e : Fin n → Entry) : Prop :=
  ∀ i, (e i).1 ≤ i.val

private def Pairwise {n : ℕ} (R : Entry → Entry → Prop) (e : Fin n → Entry) : Prop :=
  ∀ ⦃i j⦄, i < j → R (e i) (e j)

private def Unbarred {n : ℕ} (e : Fin n → Entry) : Prop :=
  ∀ i, (e i).2 = false

private abbrev Avoiders (R : Entry → Entry → Prop) (n : ℕ) :=
  {e : Fin n → Entry // Bounded e ∧ Pairwise R e}

private abbrev WithBar (R : Entry → Entry → Prop) (n : ℕ) :=
  {e : Avoiders R n // ¬ Unbarred e.val}

private theorem avoids_iff {n : ℕ} (B : Finset SignedPattern2) (R : Entry → Entry → Prop)
    (pair : ∀ x y : Entry, ⟨compare x.1 y.1, x.2, y.2⟩ ∉ B ↔ R x y) (e : Fin n → Entry) :
    (∀ p ∈ B, ¬ SignedInvSeqContains e p) ↔ Pairwise R e := by
  constructor
  · intro h i j hij
    exact (pair _ _).mp fun hm => h _ hm ⟨i, j, hij, rfl, rfl, rfl⟩
  · rintro h p hm ⟨i, j, hij, ho, hs, ht⟩
    apply (pair _ _).mpr (h hij)
    cases p
    simpa only [ho, hs, ht] using hm

private theorem suffix_allowed_iff (b : Bool) (x y : Entry) :
    ⟨compare x.1 y.1, x.2, y.2⟩ ∉ suffixPatterns b ↔ SuffixAllowed b x y := by
  cases b <;> cases hx : x.2 <;> cases hy : y.2 <;>
    simp [suffixPatterns, SuffixAllowed, hx, hy, SignedPattern2.mk.injEq,
      compare_lt_iff_lt, and_comm]

private theorem prefix_allowed_iff (x y : Entry) :
    ⟨compare x.1 y.1, x.2, y.2⟩ ∉ prefixPatterns ↔ PrefixAllowed x y := by
  cases hx : x.2 <;> cases hy : y.2 <;>
    simp [prefixPatterns, PrefixAllowed, hx, hy, SignedPattern2.mk.injEq,
      compare_lt_iff_lt, and_comm]

private theorem count_eq_card (B : Finset SignedPattern2) (R : Entry → Entry → Prop)
    (pair : ∀ x y : Entry, ⟨compare x.1 y.1, x.2, y.2⟩ ∉ B ↔ R x y) (n : ℕ) :
    signedInvAvoidCount B n = Nat.card (Avoiders R n) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun e => and_congr_right' (avoids_iff B R pair e))

private instance avoidersFinite (R : Entry → Entry → Prop) (n : ℕ) : Finite (Avoiders R n) :=
  Finite.of_injective
    (fun (e : Avoiders R n) (i : Fin n) =>
      ((⟨(e.val i).1, Nat.lt_succ_of_le (e.property.1 i)⟩ : Fin (i.val + 1)), (e.val i).2))
    (by
      intro e f h
      apply Subtype.ext
      funext i
      exact Prod.ext (congrArg (fun a => (a i).1.val) h) (congrArg (fun a => (a i).2) h))

-- The all-unbarred avoiders are the ordinary inversion sequences.
private def unbarredEquiv {R : Entry → Entry → Prop}
    (plain : ∀ a b, R (a, false) (b, false)) (n : ℕ) :
    {e : Avoiders R n // Unbarred e.val} ≃ ((i : Fin n) → Fin (i.val + 1)) where
  toFun e i := ⟨(e.val.val i).1, Nat.lt_succ_of_le (e.val.property.1 i)⟩
  invFun a := ⟨⟨fun i => ((a i).val, false), fun i => Nat.le_of_lt_succ (a i).isLt,
    fun {i j} _ => plain (a i).val (a j).val⟩, fun _ => rfl⟩
  left_inv e := Subtype.ext (Subtype.ext (funext fun i => Prod.ext rfl (e.property i).symm))
  right_inv a := by rfl

private theorem card_succ {R : Entry → Entry → Prop} (plain : ∀ a b, R (a, false) (b, false))
    {n : ℕ} (step : Avoiders R n ≃ WithBar R (n + 1)) :
    Nat.card (Avoiders R (n + 1)) = Nat.card (Avoiders R n) + (n + 1)! := by
  classical
  rw [← Nat.card_congr (Equiv.sumCompl (fun e : Avoiders R (n + 1) => Unbarred e.val)),
    Nat.card_sum, Nat.card_congr (unbarredEquiv plain (n + 1)), ← Nat.card_congr step,
    Nat.card_pi]
  simp only [Nat.card_fin]
  rw [Fin.prod_univ_eq_prod_range fun i => i + 1, Finset.prod_range_add_one_eq_factorial, add_comm]

private theorem count_factorial_sum (B : Finset SignedPattern2) (R : Entry → Entry → Prop)
    (pair : ∀ x y : Entry, ⟨compare x.1 y.1, x.2, y.2⟩ ∉ B ↔ R x y)
    (plain : ∀ a b, R (a, false) (b, false))
    (step : ∀ n, Avoiders R n ≃ WithBar R (n + 1)) (n : ℕ) :
    signedInvAvoidCount B n = ∑ i ∈ Finset.range (n + 1), i ! := by
  induction n with
  | zero => simp [signedInvAvoidCount_zero]
  | succ n ih =>
    rw [count_eq_card B R pair, card_succ plain (step n), ← count_eq_card B R pair, ih,
      Finset.sum_range_succ (fun i => i !) (n + 1)]

private theorem magnitude_zero {n : ℕ} (e : Fin (n + 1) → Entry) (h : Bounded e) :
    (e 0).1 = 0 :=
  Nat.eq_zero_of_le_zero (h 0)

private theorem barred_zero {b : Bool} {n : ℕ} (e : Avoiders (SuffixAllowed b) (n + 1))
    {i : Fin (n + 1)} (hi : (e.val i).2 = true) : (e.val i).1 = 0 := by
  rcases (Fin.zero_le i).eq_or_lt with he | hlt
  · exact he ▸ magnitude_zero e.val e.property.1
  · exact Nat.eq_zero_of_le_zero
      ((e.property.2 hlt).1 (Or.inr hi) |>.trans (magnitude_zero e.val e.property.1).le)

private noncomputable def lastSign (b : Bool) {n : ℕ} (e : Fin n → Entry) : Bool := by
  classical
  exact if Unbarred e then true else b

private theorem snoc_pairs {n : ℕ} {R : Entry → Entry → Prop} {e : Fin n → Entry}
    {x : Entry} (h : Pairwise R e) (hx : ∀ i, R (e i) x) : Pairwise R (Fin.snoc e x) := by
  intro i j
  induction i using Fin.lastCases with
  | last => exact fun hij => ((Fin.le_last j).not_gt hij).elim
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa using fun _ : i.castSucc < Fin.last n => hx i
    | cast j =>
      simpa only [Fin.snoc_castSucc, Fin.castSucc_lt_castSucc_iff] using
        fun hij : i < j => h hij

-- Removing the final zero of a word with a bar is inverted by appending a zero.
-- Its sign is barred if it is the first bar, and otherwise is prescribed by the class.
private noncomputable def appendZero (b : Bool) {n : ℕ} (e : Avoiders (SuffixAllowed b) n) :
    WithBar (SuffixAllowed b) (n + 1) := by
  refine ⟨⟨Fin.snoc e.val (0, lastSign b e.val), ?_, snoc_pairs e.property.2 ?_⟩, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simpa [Fin.snoc_castSucc] using e.property.1 i
  · intro i
    refine ⟨fun _ => Nat.zero_le _, fun hi _ => ?_⟩
    have hn : ¬ Unbarred e.val := fun h => Bool.false_ne_true ((h i).symm.trans hi)
    classical
    simp [lastSign, hn]
  · intro h
    have hu : Unbarred e.val := fun i => by simpa using h i.castSucc
    classical
    simpa [lastSign, hu] using h (Fin.last n)

private def removeLast (b : Bool) {n : ℕ} (e : WithBar (SuffixAllowed b) (n + 1)) :
    Avoiders (SuffixAllowed b) n :=
  ⟨Fin.init e.val.val, fun i => e.val.property.1 i.castSucc,
    fun {i j} hij => e.val.property.2 (show i.castSucc < j.castSucc from
      Fin.castSucc_lt_castSucc_iff.mpr hij)⟩

private noncomputable def suffixStep (b : Bool) (n : ℕ) :
    Avoiders (SuffixAllowed b) n ≃ WithBar (SuffixAllowed b) (n + 1) where
  toFun := appendZero b
  invFun := removeLast b
  left_inv e := by
    apply Subtype.ext
    change Fin.init (α := fun _ => Entry) (Fin.snoc e.val (0, lastSign b e.val)) = e.val
    rw [Fin.init_snoc]
  right_inv e := by
    classical
    have last : e.val.val (Fin.last n) = (0, lastSign b (Fin.init e.val.val)) := by
      by_cases hu : Unbarred (Fin.init e.val.val)
      · have hb : (e.val.val (Fin.last n)).2 = true := by
          cases hs : (e.val.val (Fin.last n)).2
          · exfalso
            apply e.property
            intro i
            induction i using Fin.lastCases with
            | last => exact hs
            | cast i => exact hu i
          · rfl
        exact Prod.ext (barred_zero e.val hb) (by simp [lastSign, hu, hb])
      · obtain ⟨i, hi⟩ : ∃ i : Fin n, (e.val.val i.castSucc).2 = true := by
          simpa [Unbarred, Fin.init] using hu
        have hzero := barred_zero e.val hi
        have hp := e.val.property.2 i.castSucc_lt_last
        have hz := Nat.eq_zero_of_le_zero ((hp.1 (Or.inl hi)).trans hzero.le)
        exact Prod.ext hz (by simpa [lastSign, hu] using hp.2 hi (hzero.trans hz.symm))
    apply Subtype.ext
    apply Subtype.ext
    change Fin.snoc (Fin.init e.val.val) (0, lastSign b (Fin.init e.val.val)) = e.val.val
    rw [← last, Fin.snoc_init_self]

private theorem prefix_cons {n : ℕ} {e : Fin n → Entry} (h : Pairwise PrefixAllowed e)
    (he : ∀ i, 0 < (e i).1) : Pairwise PrefixAllowed (Fin.cons (0, true) e) := by
  intro i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp
    | succ j => simpa [PrefixAllowed] using (he j).ne
  | succ i =>
    induction j using Fin.cases with
    | zero => simp
    | succ j => simpa [Fin.succ_lt_succ_iff] using fun hij : i < j => h hij

private theorem prefix_shift_iff (x y : Entry) :
    PrefixAllowed (x.1 + 1, x.2) (y.1 + 1, y.2) ↔ PrefixAllowed x y := by
  simp [PrefixAllowed]

-- A word with a bar starts with barred zero, and all other magnitudes are positive.
private theorem first_bar {n : ℕ} (e : WithBar PrefixAllowed (n + 1)) :
    (e.val.val 0).2 = true := by
  cases hs : (e.val.val 0).2
  · exfalso
    apply e.property
    intro i
    induction i using Fin.cases with
    | zero => exact hs
    | succ i =>
      cases hi : (e.val.val i.succ).2
      · rfl
      · have hp := e.val.property.2 (Fin.succ_pos i)
        have hz := magnitude_zero e.val.val e.val.property.1
        have heq := Nat.eq_zero_of_le_zero ((hp.2 hs hi).trans hz.le)
        exact (hp.1 (Or.inr hi) (hz.trans heq.symm)).elim
  · rfl

private theorem tail_pos {n : ℕ} (e : WithBar PrefixAllowed (n + 1)) (i : Fin n) :
    0 < (e.val.val i.succ).1 := by
  have hne := (e.val.property.2 (Fin.succ_pos i)).1 (Or.inl (first_bar e))
  rw [magnitude_zero e.val.val e.val.property.1] at hne
  exact Nat.pos_of_ne_zero hne.symm

private def prependZero {n : ℕ} (e : Avoiders PrefixAllowed n) :
    WithBar PrefixAllowed (n + 1) := by
  let shift (i : Fin n) : Entry := ((e.val i).1 + 1, (e.val i).2)
  refine ⟨⟨Fin.cons (0, true) shift, ?_, prefix_cons ?_ (fun i => Nat.succ_pos _)⟩, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simp
    | succ i => exact Nat.succ_le_succ (e.property.1 i)
  · intro i j hij
    exact (prefix_shift_iff _ _).mpr (e.property.2 hij)
  · intro h
    exact Bool.false_ne_true (h 0).symm

private def removeFirst {n : ℕ} (e : WithBar PrefixAllowed (n + 1)) :
    Avoiders PrefixAllowed n := by
  let tail (i : Fin n) : Entry := ((e.val.val i.succ).1 - 1, (e.val.val i.succ).2)
  have shift (i : Fin n) : ((tail i).1 + 1, (tail i).2) = e.val.val i.succ :=
    Prod.ext (Nat.sub_add_cancel (tail_pos e i)) rfl
  refine ⟨tail, fun i => Nat.sub_le_of_le_add (e.val.property.1 i.succ), ?_⟩
  intro i j hij
  apply (prefix_shift_iff _ _).mp
  rw [shift i, shift j]
  exact e.val.property.2 (Fin.succ_lt_succ_iff.mpr hij)

private def prefixStep (n : ℕ) : Avoiders PrefixAllowed n ≃ WithBar PrefixAllowed (n + 1) where
  toFun := prependZero
  invFun := removeFirst
  left_inv e := by
    apply Subtype.ext
    funext i
    exact Prod.ext (Nat.add_sub_cancel _ _) rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    induction i using Fin.cases with
    | zero => exact Prod.ext (magnitude_zero e.val.val e.val.property.1).symm (first_bar e).symm
    | succ i => exact Prod.ext (Nat.sub_add_cancel (tail_pos e i)) rfl

private theorem suffix_count (b : Bool) (n : ℕ) :
    signedInvAvoidCount (suffixPatterns b) n = ∑ i ∈ Finset.range (n + 1), i ! :=
  count_factorial_sum _ _ (suffix_allowed_iff b) (by simp [SuffixAllowed]) (suffixStep b) n

private theorem prefix_count (n : ℕ) :
    signedInvAvoidCount prefixPatterns n = ∑ i ∈ Finset.range (n + 1), i ! :=
  count_factorial_sum _ _ prefix_allowed_iff (by simp [PrefixAllowed]) prefixStep n

end signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1

open signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1 in
/-- **Mansour–Safadi Theorem 3, class C3 (signed patterns 0̄1̄, 0̄0̄, 0̄1, 01̄).** A signed
inversion sequence of length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1,
\dots, k - 1, \overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$,
$01$, $10$, each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as
$|\tau_1|$, $|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write
$\bar I_n(B)$ for the set of signed inversion sequences of length $n$ that avoid every pattern in
$B$. Let $B_1 = \{\bar 0\bar 1, \bar 0\bar 0, \bar 0 1, 0\bar 1\}$,
$B_2 = \{\bar 0\bar 1, \bar 0 0, \bar 0 1, 0\bar 1\}$ and
$B_3 = \{\bar 0\bar 0, \bar 0 0, 0\bar 1, 0\bar 0\}$. For every $n \ge 0$,
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = |\bar I_n(B_3)| = \sum_{i=0}^{n} i!$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C3) (`integers-2026-A74-thm-3`). -/
public theorem signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.lt, false, true⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩} ∧
    ∀ n, signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} n =
      ∑ i ∈ Finset.range (n + 1), i ! := by
  refine ⟨funext fun n => ?_, funext fun n => ?_, suffix_count false⟩
  · exact (suffix_count false n).trans (suffix_count true n).symm
  · exact (suffix_count true n).trans (prefix_count n).symm

end MetaMathlibExt
