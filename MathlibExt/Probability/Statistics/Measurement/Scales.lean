/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Expect

import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Ordinal scales: ranks, order statistics and medians

This file formalizes the Stevens (1946) ordinal-scale laws: for a finite
sample in a linear order, rank comparisons are invariant under strictly
increasing maps, while order statistics (hence medians) commute with
(are equivariant under) monotone maps, hence in particular strictly
increasing ones; only the positions of order statistics are invariant.

A sample is a family `x : Fin n → α` of values in a linear order; ties are
allowed. Ranks use the competition (minimum-rank) convention: tied subjects
share the smallest rank of their tie group. For even sample sizes the middle
value is not unique, so medians are the lower and upper order statistics, never
the average of the two middle values (which is not invariant).

The file also formalizes an ordinal-scale failure for means: a strictly
increasing recoding can reverse a group-mean comparison. Interval- and
ratio-scale affine laws live in the sibling module `AffineLaws`. Main results:
`sampleRank_lt_sampleRank_iff`, `sampleRank_comp_of_strictMono`,
`monotone_orderStatistic`, `orderStatistic_comp_of_monotone`,
`lowerMedian_comp_of_monotone`, `upperMedian_comp_of_monotone` and
`exists_strictMono_reverses_groupMean`.

## References

* S. S. Stevens, *On the Theory of Scales of Measurement*,
  Science 103(2684) (7 June 1946), 677-680.
* R. V. Hogg, J. W. McKean and A. T. Craig, *Introduction to Mathematical
  Statistics*, 7th edition, Pearson, 2013, Theorem 1.9.1.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

/-- Competition (minimum) rank of subject `i`: one plus the number of subjects
strictly below `x i`. Tied subjects share the smallest rank of their group. -/
def sampleRank {n : ℕ} {α : Type*} [LinearOrder α] (x : Fin n → α)
    (i : Fin n) : ℕ :=
  1 + (Finset.univ.filter (fun k => x k < x i)).card

/-- The `k`-th order statistic: the `k`-th smallest value of `x` counted with
multiplicity (0-based), via Mathlib's `Tuple.sort`. -/
def orderStatistic {n : ℕ} {α : Type*} [LinearOrder α] (x : Fin n → α)
    (k : Fin n) : α :=
  x (Tuple.sort x k)

/-- Lower median of a nonempty sample: the order statistic at index `n / 2`. -/
def lowerMedian {n : ℕ} {α : Type*} [LinearOrder α]
    (x : Fin (n + 1) → α) : α :=
  orderStatistic x ⟨n / 2, by omega⟩

/-- Upper median of a nonempty sample: the order statistic at index
`(n + 1) / 2`. Agrees with `lowerMedian` for odd sample sizes. -/
def upperMedian {n : ℕ} {α : Type*} [LinearOrder α]
    (x : Fin (n + 1) → α) : α :=
  orderStatistic x ⟨(n + 1) / 2, by omega⟩

/-- The order statistics form the monotone (sorted) rearrangement of `x`. -/
theorem monotone_orderStatistic {n : ℕ} {α : Type*} [LinearOrder α]
    (x : Fin n → α) : Monotone (orderStatistic x) :=
  Tuple.monotone_sort x

/-- Rank comparisons agree with value comparisons. -/
theorem sampleRank_lt_sampleRank_iff {n : ℕ} {α : Type*} [LinearOrder α]
    (x : Fin n → α) (i j : Fin n) :
    sampleRank x i < sampleRank x j ↔ x i < x j := by
  constructor
  · intro h
    by_contra hcon
    have hle : x j ≤ x i := le_of_not_gt hcon
    have hsub : Finset.univ.filter (fun k => x k < x j) ⊆
        Finset.univ.filter (fun k => x k < x i) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact lt_of_lt_of_le hk hle
    have hcard := Finset.card_le_card hsub
    have hle_rank : sampleRank x j ≤ sampleRank x i := by
      unfold sampleRank
      exact Nat.add_le_add_left hcard _
    omega
  · intro hlt
    have hsub : Finset.univ.filter (fun k => x k < x i) ⊆
        Finset.univ.filter (fun k => x k < x j) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact lt_trans hk hlt
    have hmem : i ∈ Finset.univ.filter (fun k => x k < x j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt
    have hnotmem : i ∉ Finset.univ.filter (fun k => x k < x i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_irrefl _
    have hssub := (Finset.ssubset_iff_of_subset hsub).mpr ⟨i, hmem, hnotmem⟩
    have hcard := Finset.card_lt_card hssub
    unfold sampleRank
    exact Nat.add_lt_add_left hcard _

/-- Ranks are invariant under strictly increasing maps. -/
theorem sampleRank_comp_of_strictMono {n : ℕ} {α β : Type*} [LinearOrder α]
    [LinearOrder β] {x : Fin n → α} {f : α → β} (hf : StrictMono f)
    (i : Fin n) : sampleRank (f ∘ x) i = sampleRank x i := by
  have h : Finset.univ.filter (fun k => (f ∘ x) k < (f ∘ x) i) =
      Finset.univ.filter (fun k => x k < x i) := by
    apply Finset.filter_congr
    intro k _
    exact StrictMono.lt_iff_lt hf
  unfold sampleRank
  rw [h]

/-- Order statistics commute with monotone maps, hence with strictly
increasing maps via `StrictMono.monotone`. -/
theorem orderStatistic_comp_of_monotone {n : ℕ} {α β : Type*} [LinearOrder α]
    [LinearOrder β] {x : Fin n → α} {f : α → β} (hf : Monotone f)
    (k : Fin n) : orderStatistic (f ∘ x) k = f (orderStatistic x k) := by
  have hcomp : Monotone ((f ∘ x) ∘ Tuple.sort x) :=
    hf.comp (Tuple.monotone_sort x)
  have huniq := Tuple.unique_monotone (Tuple.monotone_sort (f ∘ x)) hcomp
  have hk := congrFun huniq k
  unfold orderStatistic
  exact hk

/-- The lower median commutes with monotone maps. -/
theorem lowerMedian_comp_of_monotone {n : ℕ} {α β : Type*} [LinearOrder α]
    [LinearOrder β] {x : Fin (n + 1) → α} {f : α → β} (hf : Monotone f) :
    lowerMedian (f ∘ x) = f (lowerMedian x) := by
  unfold lowerMedian
  exact orderStatistic_comp_of_monotone hf _

/-- The upper median commutes with monotone maps. -/
theorem upperMedian_comp_of_monotone {n : ℕ} {α β : Type*} [LinearOrder α]
    [LinearOrder β] {x : Fin (n + 1) → α} {f : α → β} (hf : Monotone f) :
    upperMedian (f ∘ x) = f (upperMedian x) := by
  unfold upperMedian
  exact orderStatistic_comp_of_monotone hf _

open scoped BigOperators

/-- The `min` recoding `min (2 * t) ((t + 3) / 2)`, strictly increasing. -/
noncomputable def groupMeanRecode : ℝ → ℝ :=
  fun t => min (2 * t) ((t + 3) / 2)

/-- The recoding fixes `0`. -/
theorem groupMeanRecode_zero : groupMeanRecode 0 = 0 := by
  unfold groupMeanRecode
  norm_num

/-- The recoding sends `1` to `2`. -/
theorem groupMeanRecode_one : groupMeanRecode 1 = 2 := by
  unfold groupMeanRecode
  norm_num

/-- The recoding fixes `3`. -/
theorem groupMeanRecode_three : groupMeanRecode 3 = 3 := by
  unfold groupMeanRecode
  norm_num

/-- The `min` recoding is strictly increasing, by cases on `t ≤ 1`. -/
private theorem groupMeanRecode_strictMono :
    StrictMono groupMeanRecode := by
  intro a b hab
  unfold groupMeanRecode
  by_cases hb : b ≤ 1
  · have ha : a ≤ 1 := le_trans (le_of_lt hab) hb
    have h1 : min (2 * a) ((a + 3) / 2) = 2 * a := by
      apply min_eq_left
      linarith
    have h2 : min (2 * b) ((b + 3) / 2) = 2 * b := by
      apply min_eq_left
      linarith
    rw [h1, h2]
    linarith
  · by_cases ha : (1 : ℝ) ≤ a
    · have h1 : min (2 * a) ((a + 3) / 2) = (a + 3) / 2 := by
        apply min_eq_right
        linarith
      have h2 : min (2 * b) ((b + 3) / 2) = (b + 3) / 2 := by
        apply min_eq_right
        have hb1 : (1 : ℝ) < b := lt_of_le_of_lt ha hab
        linarith
      rw [h1, h2]
      linarith
    · have ha1 : a < 1 := lt_of_not_ge ha
      have hb1 : (1 : ℝ) < b := lt_of_not_ge hb
      have h1 : min (2 * a) ((a + 3) / 2) = 2 * a := by
        apply min_eq_left
        linarith
      have h2 : min (2 * b) ((b + 3) / 2) = (b + 3) / 2 := by
        apply min_eq_right
        linarith
      rw [h1, h2]
      linarith

/-- Pooled sample `![0, 3, 1, 1]` for the reversal witness. -/
def groupMeanX : Fin 4 → ℝ := ![0, 3, 1, 1]

/-- First group `{0, 1}` for the reversal witness. -/
def groupMeanA : Finset (Fin 4) := {0, 1}

/-- Second group `{2, 3}` for the reversal witness. -/
def groupMeanB : Finset (Fin 4) := {2, 3}

/-- Mean of the witness sample on group `A`. -/
theorem groupMean_meanA : 𝔼 i ∈ groupMeanA, groupMeanX i = 3 / 2 := by
  rw [Finset.expect_eq_sum_div_card]
  have hsum : ∑ i ∈ groupMeanA, groupMeanX i = 3 := by
    have h0 : groupMeanX 0 = (0 : ℝ) := by simp [groupMeanX]
    have h1 : groupMeanX 1 = (3 : ℝ) := by simp [groupMeanX]
    unfold groupMeanA
    rw [Finset.sum_pair (by decide : (0 : Fin 4) ≠ 1), h0, h1]
    norm_num
  have hcard : (groupMeanA.card : ℝ) = 2 := by
    unfold groupMeanA
    rw [Finset.card_pair (by decide : (0 : Fin 4) ≠ 1)]
    norm_num
  rw [hsum, hcard]

/-- Mean of the witness sample on group `B`. -/
theorem groupMean_meanB : 𝔼 i ∈ groupMeanB, groupMeanX i = 1 := by
  rw [Finset.expect_eq_sum_div_card]
  have hsum : ∑ i ∈ groupMeanB, groupMeanX i = 2 := by
    have h2 : groupMeanX 2 = (1 : ℝ) := by simp [groupMeanX]
    have h3 : groupMeanX 3 = (1 : ℝ) := by simp [groupMeanX]
    unfold groupMeanB
    rw [Finset.sum_pair (by decide : (2 : Fin 4) ≠ 3), h2, h3]
    norm_num
  have hcard : (groupMeanB.card : ℝ) = 2 := by
    unfold groupMeanB
    rw [Finset.card_pair (by decide : (2 : Fin 4) ≠ 3)]
    norm_num
  rw [hsum, hcard]
  norm_num

/-- Mean of the recoded witness sample on group `A`. -/
theorem groupMean_recodeMeanA :
    𝔼 i ∈ groupMeanA, groupMeanRecode (groupMeanX i) = 3 / 2 := by
  rw [Finset.expect_eq_sum_div_card]
  have hsum : ∑ i ∈ groupMeanA, groupMeanRecode (groupMeanX i) = 3 := by
    have h0 : groupMeanX 0 = (0 : ℝ) := by simp [groupMeanX]
    have h1 : groupMeanX 1 = (3 : ℝ) := by simp [groupMeanX]
    unfold groupMeanA
    rw [Finset.sum_pair (by decide : (0 : Fin 4) ≠ 1), h0, h1,
      groupMeanRecode_zero, groupMeanRecode_three]
    norm_num
  have hcard : (groupMeanA.card : ℝ) = 2 := by
    unfold groupMeanA
    rw [Finset.card_pair (by decide : (0 : Fin 4) ≠ 1)]
    norm_num
  rw [hsum, hcard]

/-- Mean of the recoded witness sample on group `B`. -/
theorem groupMean_recodeMeanB :
    𝔼 i ∈ groupMeanB, groupMeanRecode (groupMeanX i) = 2 := by
  rw [Finset.expect_eq_sum_div_card]
  have hsum : ∑ i ∈ groupMeanB, groupMeanRecode (groupMeanX i) = 4 := by
    have h2 : groupMeanX 2 = (1 : ℝ) := by simp [groupMeanX]
    have h3 : groupMeanX 3 = (1 : ℝ) := by simp [groupMeanX]
    unfold groupMeanB
    rw [Finset.sum_pair (by decide : (2 : Fin 4) ≠ 3), h2, h3,
      groupMeanRecode_one]
    norm_num
  have hcard : (groupMeanB.card : ℝ) = 2 := by
    unfold groupMeanB
    rw [Finset.card_pair (by decide : (2 : Fin 4) ≠ 3)]
    norm_num
  rw [hsum, hcard]
  norm_num

/-- Competition ranks of the witness sample. -/
theorem groupMean_ranks :
    sampleRank groupMeanX 0 = 1 ∧ sampleRank groupMeanX 1 = 4 ∧
    sampleRank groupMeanX 2 = 2 ∧ sampleRank groupMeanX 3 = 2 := by
  have h0 : groupMeanX 0 = (0 : ℝ) := by simp [groupMeanX]
  have h1 : groupMeanX 1 = (3 : ℝ) := by simp [groupMeanX]
  have hcases : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    intro k
    fin_cases k <;> decide
  have hempty : Finset.univ.filter (fun k => groupMeanX k < groupMeanX 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro k _ hk
    rw [h0] at hk
    have hnn : (0 : ℝ) ≤ groupMeanX k := by
      rcases hcases k with rfl | rfl | rfl | rfl <;> norm_num [groupMeanX]
    linarith
  have hset1 : Finset.univ.filter (fun k => groupMeanX k < groupMeanX 1) = {0, 2, 3} := by
    rw [h1]
    ext k
    rcases hcases k with rfl | rfl | rfl | rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact ⟨fun _ => Or.inl trivial, fun _ => by norm_num [groupMeanX]⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact ⟨fun h => by simp [groupMeanX] at h, fun h => absurd h (by decide)⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact ⟨fun _ => Or.inr (Or.inl trivial), fun _ => by norm_num [groupMeanX]⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact ⟨fun _ => Or.inr (Or.inr trivial), fun _ => by norm_num [groupMeanX]⟩
  have hset2 : Finset.univ.filter (fun k => groupMeanX k < groupMeanX 2) = {0} := by
    have h2 : groupMeanX 2 = (1 : ℝ) := by simp [groupMeanX]
    rw [h2]
    ext k
    rcases hcases k with rfl | rfl | rfl | rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun _ => trivial, fun _ => by norm_num [groupMeanX]⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => by simp [groupMeanX] at h, fun h => absurd h (by decide)⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => by simp [groupMeanX] at h, fun h => absurd h (by decide)⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => by simp [groupMeanX] at h, fun h => absurd h (by decide)⟩
  have hset3 : Finset.univ.filter (fun k => groupMeanX k < groupMeanX 3) = {0} := by
    have h3 : groupMeanX 3 = (1 : ℝ) := by simp [groupMeanX]
    rw [h3]
    ext k
    rcases hcases k with rfl | rfl | rfl | rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun _ => trivial, fun _ => by norm_num [groupMeanX]⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => by simp [groupMeanX] at h, fun h => absurd h (by decide)⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => by simp [groupMeanX] at h, fun h => absurd h (by decide)⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => by simp [groupMeanX] at h, fun h => absurd h (by decide)⟩
  have r0 : sampleRank groupMeanX 0 = 1 := by
    unfold sampleRank
    rw [hempty, Finset.card_empty, add_zero]
  have r1 : sampleRank groupMeanX 1 = 4 := by
    unfold sampleRank
    rw [hset1]
    decide
  have r2 : sampleRank groupMeanX 2 = 2 := by
    unfold sampleRank
    rw [hset2]
    decide
  have r3 : sampleRank groupMeanX 3 = 2 := by
    unfold sampleRank
    rw [hset3]
    decide
  exact ⟨r0, r1, r2, r3⟩

/-- A strictly increasing recoding can reverse a group-mean comparison
while preserving all individual ranks; rank preservation follows from
`StrictMono f` via `sampleRank_comp_of_strictMono`. -/
theorem exists_strictMono_reverses_groupMean :
    ∃ (f : ℝ → ℝ) (x : Fin 4 → ℝ) (A B : Finset (Fin 4)),
      StrictMono f ∧
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      (∀ i, sampleRank (f ∘ x) i = sampleRank x i) ∧
      (𝔼 i ∈ B, x i < 𝔼 i ∈ A, x i) ∧
      (𝔼 i ∈ A, f (x i) < 𝔼 i ∈ B, f (x i)) := by
  refine ⟨groupMeanRecode, groupMeanX, groupMeanA, groupMeanB,
    groupMeanRecode_strictMono, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.insert_nonempty 0 {1}
  · exact Finset.insert_nonempty 2 {3}
  · unfold groupMeanA groupMeanB
    rw [Finset.disjoint_left]
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl <;> decide
  · intro i
    exact sampleRank_comp_of_strictMono groupMeanRecode_strictMono i
  · rw [groupMean_meanB, groupMean_meanA]
    norm_num
  · rw [groupMean_recodeMeanA, groupMean_recodeMeanB]
    norm_num

end MathlibExt.Probability.Statistics.Measurement
