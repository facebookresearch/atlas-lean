/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BloomFilterFalsePositive
public meta import CSLibExt.Algorithms.Lean.DataStructures.BloomFilterFalsePositive

/-!
# Bloom-filter false-positive tests

Executed fixtures: a filter with two hash functions on `Nat` into `8` bits, after inserting
`[1, 2]`, reports `1`, `2` and the colliding `9` present and `4` absent, matching the
characterisation `mayContain_insertAll_empty_iff`. Counting: with `m = 3`, `n = 1`, `k = 2`
exactly `4 = 2 ^ 2` stored-hash outcomes leave bit `0` unset. Strict gap: with `m = 2`,
`n = 1`, `k = 2` the exact false-positive rate is `10 / 16 = 5 / 8`, strictly above Bloom's
formula `(1 - (1/2) ^ 2) ^ 2 = 9 / 16`. Boundary: `k = 0` gives rate `1`; `m = 0` gives the junk
value `0`. Optimal `k`: `log t · log (1 - t)` attains `(log 2) ^ 2` at `t = 1 / 2` and stays
strictly below it at `t = 1 / 4`; for `m = 8`, `n = 1` the approximation at `κ = 8 log 2` is at
most its value at `κ = 3`. Axiom audit follows.
-/

namespace Cslib.Algorithms.Lean.BloomFilter

open Finset

/-- Two hash functions into `8` bits. -/
def testHashes : List (Nat → Fin 8) := [fun x => ⟨x % 8, Nat.mod_lt _ (by decide)⟩,
  fun x => ⟨(3 * x) % 8, Nat.mod_lt _ (by decide)⟩]

/-- The filter after inserting `1` and `2`. -/
def testFilter : BloomFilter Nat 8 := (empty testHashes).insertAll [1, 2]

#guard testFilter.mayContain 1
#guard testFilter.mayContain 2
#guard testFilter.mayContain 9
#guard !testFilter.mayContain 4

example : testFilter.mayContain 9 = true ↔
    ∀ h ∈ testHashes, ∃ x ∈ [1, 2], ∃ h' ∈ testHashes, h' x = h 9 :=
  mayContain_insertAll_empty_iff testHashes [1, 2] 9

example : #{H : Fin 1 → Fin 2 → Fin 3 | (0 : Fin 3) ∉ setBits H} = 4 := by
  rw [card_unset]; norm_num

example : #{H : Fin 1 → Fin 2 → Fin 3 | (0 : Fin 3) ∉ setBits H} = 4 := by decide

/-- The exact rate for `m = 2`, `n = 1`, `k = 2` is `5 / 8`. -/
theorem falsePositiveProb_two_one_two : falsePositiveProb 2 1 2 = 5 / 8 := by
  have hcard : #{Hq : (Fin 1 → Fin 2 → Fin 2) × (Fin 2 → Fin 2) |
      ∀ j, Hq.2 j ∈ setBits Hq.1} = 10 := by decide
  unfold falsePositiveProb
  rw [hcard]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  norm_num

/-- Bloom's formula is strictly below the exact rate in this instance. -/
example : (1 - (1 - 1 / (2 : ℝ)) ^ (1 * 2)) ^ 2 < falsePositiveProb 2 1 2 := by
  rw [falsePositiveProb_two_one_two]
  norm_num

example : (1 - (1 - 1 / (2 : ℝ)) ^ (1 * 2)) ^ 2 ≤ falsePositiveProb 2 1 2 :=
  classical_le_falsePositiveProb (by decide)

/-- Junk value outside the domain `0 < m`: with no bits the outcome space is empty and the
counting ratio is `0 / 0 = 0`. -/
example : falsePositiveProb 0 1 1 = 0 := by
  simp [falsePositiveProb]

example : falsePositiveProb 5 3 0 = 1 := by
  rw [falsePositiveProb_eq (by decide)]
  simp

example : Real.log (1 / 2) * Real.log (1 - 1 / 2) = Real.log 2 ^ 2 :=
  (log_mul_log_one_sub_eq_iff (by norm_num) (by norm_num)).mpr rfl

example : Real.log (1 / 4) * Real.log (1 - 1 / 4) < Real.log 2 ^ 2 :=
  lt_of_le_of_ne (log_mul_log_one_sub_le (by norm_num) (by norm_num))
    ((log_mul_log_one_sub_eq_iff (by norm_num) (by norm_num)).not.mpr (by norm_num))

example : expApprox 8 1 (((8 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * Real.log 2) ≤ expApprox 8 1 3 :=
  expApprox_optimal (by decide) (by decide) (by norm_num)

example : expApprox 8 1 (((8 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * Real.log 2) =
    (1 / 2) ^ (((8 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * Real.log 2) :=
  expApprox_at_optimum (by decide) (by decide)

#print axioms bit_insertAll_iff
#print axioms mayContain_insertAll_empty_iff
#print axioms card_unset
#print axioms prob_unset
#print axioms expected_fraction_set
#print axioms falsePositiveProb_eq
#print axioms classical_le_falsePositiveProb
#print axioms exp_approx_le_falsePositiveProb
#print axioms log_mul_log_one_sub_le
#print axioms log_mul_log_one_sub_eq_iff
#print axioms expApprox_at_optimum
#print axioms expApprox_optimal

end Cslib.Algorithms.Lean.BloomFilter
