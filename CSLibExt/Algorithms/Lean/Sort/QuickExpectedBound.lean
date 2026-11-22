/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.Quick
public import CSLibExt.Algorithms.Lean.Random.RandomlyPermute.Probability
public import Mathlib.NumberTheory.Harmonic.Bounds
import all CSLibExt.Algorithms.Lean.Sort.QuickExpected

/-!
# Harmonic and logarithmic expected quicksort comparison bounds

Consequences of the pair-indicator analysis in `QuickExpected` (CLRS, *Introduction to
Algorithms*, fourth edition, Section 7.4). For a duplicate-free input of length `n`, the
expected comparison count is at most `2 * n * harmonic n`, hence at most
`2 * n * (1 + log n)`, and at most `6 * n * log n` for `n ≥ 2`.

The Fisher–Yates corollaries reuse the ideal shuffle's proved output law. They count only
comparisons made by the subsequent deterministic head-pivot quicksort, not shuffle work,
allocation, or total machine runtime. The shuffle uses ideal randomness, not a PRNG.
Finiteness is established in `ℝ≥0∞`, independently of the totalized `toReal` operation.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open scoped ENNReal

universe u

variable {α : Type u} [LinearOrder α]

private theorem betweenCount_eq_card {xs : List α} (hxs : xs.Nodup) (a b : α) :
    betweenCount xs a b = (xs.toFinset.filter (fun x => a < x ∧ x < b)).card := by
  rw [List.filter_toFinset, List.toFinset_card_of_nodup (hxs.filter _)]
  rfl

private theorem betweenCount_lt_length {xs : List α} (hxs : xs.Nodup)
    (a : α) {b : α} (hb : b ∈ xs) : betweenCount xs a b < xs.length := by
  rw [betweenCount_eq_card hxs, ← List.toFinset_card_of_nodup hxs]
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr
    ⟨b, List.mem_toFinset.mpr hb, by simp⟩)

private theorem betweenCount_strictMonoOn {xs : List α} (hxs : xs.Nodup) (a : α) :
    StrictMonoOn (betweenCount xs a) {b | b ∈ xs ∧ a < b} := by
  intro b hb c _ hbc
  rw [betweenCount_eq_card hxs, betweenCount_eq_card hxs]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · exact Finset.monotone_filter_right _ fun x _ hx => ⟨hx.1, hx.2.trans hbc⟩
  · intro heq
    have hmem : b ∈ xs.toFinset.filter (fun x => a < x ∧ x < c) :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hb.1, hb.2, hbc⟩
    rw [← heq] at hmem
    exact (lt_irrefl b) (Finset.mem_filter.mp hmem).2.2

private theorem sum_betweenCount_le_harmonic {xs : List α} (hxs : xs.Nodup) (a : α) :
    (∑ b ∈ xs.toFinset.filter (fun b => a < b),
      (2 : ℝ) / (betweenCount xs a b + 2)) ≤ 2 * (harmonic xs.length : ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.range xs.length, (2 : ℝ) / (k + 1) := by
      refine Finset.sum_le_sum_of_injOn (betweenCount xs a) ?_ ?_ ?_ ?_
      · intro b hb c hc heq
        simp only [Finset.mem_coe, Finset.mem_filter, List.mem_toFinset] at hb hc
        exact (betweenCount_strictMonoOn hxs a).injOn hb hc heq
      · intro k hk
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_range.mpr (betweenCount_lt_length hxs a
          (List.mem_toFinset.mp (Finset.mem_filter.mp hb).1))
      · intro b _
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      · intro k _ _
        positivity
    _ = 2 * (harmonic xs.length : ℝ) := by
      simp [harmonic, div_eq_mul_inv, Finset.mul_sum]

/-- The expected comparison count on a uniform permutation is finite, even with duplicates.
This fact is established before passing to the totalized real coercion. -/
public theorem quickSort_expectedTime_uniformPermutation_ne_top (xs : List α) :
    expectedTime quickSort (uniformPermutation xs) ≠ ⊤ := by
  rw [expectedTime_uniformPermutation]
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (by positivity))
    (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.natCast_ne_top _)

/-- The expected number of quicksort comparisons on a uniformly random permutation of a
`Nodup` list is at most `2 n H_n`. This includes the empty and singleton inputs. -/
public theorem quickSort_expectedTime_le_harmonic (xs : List α) (hxs : xs.Nodup) :
    (expectedTime quickSort (uniformPermutation xs)).toReal ≤
      2 * xs.length * (harmonic xs.length : ℝ) := by
  rw [quickSort_expectedTime_uniformPermutation_toReal xs hxs]
  calc
    _ = ∑ a ∈ xs.toFinset, ∑ b ∈ xs.toFinset.filter (fun b => a < b),
        (2 : ℝ) / (betweenCount xs a b + 2) := by
      simp only [Finset.sum_filter, Finset.sum_product]
    _ ≤ ∑ _a ∈ xs.toFinset, 2 * (harmonic xs.length : ℝ) :=
      Finset.sum_le_sum fun a _ => sum_betweenCount_le_harmonic hxs a
    _ = 2 * xs.length * (harmonic xs.length : ℝ) := by
      rw [Finset.sum_const, List.toFinset_card_of_nodup hxs]
      simp only [nsmul_eq_mul]
      ring

/-- An explicit logarithmic bound for the expected comparison count. At `n = 0` the
bound is zero; the logarithm's totalized value is multiplied by zero. -/
public theorem quickSort_expectedTime_le_log (xs : List α) (hxs : xs.Nodup) :
    (expectedTime quickSort (uniformPermutation xs)).toReal ≤
      2 * xs.length * (1 + Real.log xs.length) := by
  exact (quickSort_expectedTime_le_harmonic xs hxs).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (by positivity))

/-- A pure `n log n` comparison bound for inputs of length at least two. -/
public theorem quickSort_expectedTime_le_mul_log (xs : List α) (hxs : xs.Nodup)
    (hn : 2 ≤ xs.length) :
    (expectedTime quickSort (uniformPermutation xs)).toReal ≤
      6 * xs.length * Real.log xs.length := by
  have htwo : (2 : ℝ) ≤ xs.length := by exact_mod_cast hn
  have hlog : (1 : ℝ) / 2 ≤ Real.log xs.length := by
    calc
      _ ≤ Real.log 2 := by
        have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
        norm_num at h
        exact h
      _ ≤ _ := Real.log_le_log (by norm_num) htwo
  calc
    _ ≤ 2 * xs.length * (1 + Real.log xs.length) := quickSort_expectedTime_le_log xs hxs
    _ ≤ 2 * xs.length * (3 * Real.log xs.length) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 6 * xs.length * Real.log xs.length := by ring

/-- For any family of duplicate-free lists of length `n`, the expected quicksort comparison
count is `O(n log n)`. The family need not be sorted or have any prescribed values. -/
public theorem quickSort_expectedTime_isBigO (xs : ℕ → List α)
    (hxs : ∀ n, (xs n).Nodup) (hlen : ∀ n, (xs n).length = n) :
    (fun n => (expectedTime quickSort (uniformPermutation (xs n))).toReal)
      =O[Filter.atTop] (fun n => (n : ℝ) * Real.log n) := by
  apply Asymptotics.IsBigO.of_bound 6
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have h := quickSort_expectedTime_le_mul_log (xs n) (hxs n) (by rw [hlen]; exact hn)
  rw [hlen] at h
  have hnonneg : 0 ≤ (n : ℝ) * Real.log n :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg hnonneg, mul_assoc] using h

/-- Quicksort's expected comparison count after the ideal Fisher–Yates shuffle is finite.
Only the saved shuffled values, not the shuffle's event counters, are passed to quicksort. -/
public theorem quickSort_expectedTime_randomlyPermute_ne_top {n : ℕ} (xs : Vector α n) :
    expectedTime quickSort ((randomlyPermuteDistribution xs).map (fun r => r.ret.toList))
      ≠ ⊤ := by
  rw [randomlyPermuteDistribution_map_toList]
  exact quickSort_expectedTime_uniformPermutation_ne_top xs.toList

/-- After an ideal Fisher–Yates shuffle of a fixed duplicate-free vector, the subsequent
quicksort makes at most `2 n H_n` comparisons in expectation. This is not a bound on the
combined shuffle-plus-sort cost, and does not claim a PRNG implements the ideal law. -/
public theorem quickSort_expectedTime_randomlyPermute_le_harmonic {n : ℕ}
    (xs : Vector α n) (hxs : xs.toList.Nodup) :
    (expectedTime quickSort
      ((randomlyPermuteDistribution xs).map (fun r => r.ret.toList))).toReal ≤
      2 * n * (harmonic n : ℝ) := by
  rw [randomlyPermuteDistribution_map_toList]
  simpa only [Vector.length_toList] using quickSort_expectedTime_le_harmonic xs.toList hxs

/-- The logarithmic comparison bound after ideal Fisher–Yates, including empty input. -/
public theorem quickSort_expectedTime_randomlyPermute_le_log {n : ℕ}
    (xs : Vector α n) (hxs : xs.toList.Nodup) :
    (expectedTime quickSort
      ((randomlyPermuteDistribution xs).map (fun r => r.ret.toList))).toReal ≤
      2 * n * (1 + Real.log n) := by
  rw [randomlyPermuteDistribution_map_toList]
  simpa only [Vector.length_toList] using quickSort_expectedTime_le_log xs.toList hxs

end Cslib.Algorithms.Lean.TimeM
