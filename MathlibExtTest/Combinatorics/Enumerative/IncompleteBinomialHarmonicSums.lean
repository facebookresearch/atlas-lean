/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.IncompleteBinomialHarmonicSums
import Mathlib.Tactic.NormNum

open MathlibExt.Combinatorics.Enumerative.IncompleteBinomialHarmonicSumsWanted

-- At the upper boundary m = N = 2, the trailing coefficient `(N - 1).choose m` vanishes.
example (a : ℕ → ℝ) : a 0 + 2 * a 1 + a 2 = (a 0 + a 1) + (a 1 + a 2) := by
  have h := sum_range_choose_mul_eq_sum_range_choose_add a 2 2 (by decide) (by decide) le_rfl
  norm_num [Finset.sum_range_succ, Nat.choose] at h
  exact h

-- Below the boundary, at m = 2 and N = 3, the trailing term survives.
example (a : ℕ → ℝ) : a 0 + 3 * a 1 + 3 * a 2 = (a 0 + a 1) + 2 * (a 1 + a 2) + a 2 := by
  have h := sum_range_choose_mul_eq_sum_range_choose_add a 2 3 (by decide) (by decide) (by decide)
  norm_num [Finset.sum_range_succ, Nat.choose] at h
  exact h

-- At the zero cutoff, the extra sequence value cancels.
example (a : ℕ → ℝ) (n : ℕ) (hn : 0 < n) : a 0 = (a 0 + a 1) - a 1 := by
  simpa only [Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul]
    using sum_range_choose_two_mul_sub_one_mul_eq a 0 n hn (Nat.zero_le n)

-- At m = n = 2, the last binomial coefficient in the lower row is one.
example (a : ℕ → ℝ) : a 0 + 3 * a 1 + 3 * a 2 =
    (a 0 + a 1) + 2 * (a 1 + a 2) + (a 2 + a 3) - a 3 := by
  have h := sum_range_choose_two_mul_sub_one_mul_eq a 2 2 (by decide) le_rfl
  norm_num [Finset.sum_range_succ, Nat.choose] at h
  exact h

-- At the half-row cutoff m = n = 2, the endpoint contributes 3 * a 2.
example (a : ℕ → ℝ) : a 0 + 4 * a 1 + 6 * a 2 =
    (a 0 + a 1) + 3 * (a 1 + a 2) + 3 * a 2 := by
  have h := sum_range_choose_two_mul_mul_eq a 2 2 (by decide) (by decide) le_rfl
  norm_num [Finset.sum_range_succ, Nat.choose] at h
  exact h

-- The auxiliary sums start with an empty interval and include the upper endpoint.
example : invPowTwoSum 0 = 0 ∧ centralBinomWeightedSum 0 = 0 := by decide
example : invPowTwoSum 2 = 5 / 8 ∧ centralBinomWeightedSum 2 = 11 / 32 := by
  have h : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  norm_num [invPowTwoSum, centralBinomWeightedSum, h, Nat.choose]

-- At n = 1 only H₀ occurs and the central-binomial auxiliary sum is empty.
example : harmonic 1 - 2 * invPowTwoSum 1 + centralBinomWeightedSum 0 = 0 := by
  simpa using (sum_range_choose_two_mul_sub_one_mul_harmonic 1 (by decide)).symm

-- At n = 3 the half-row contributes 5 H₁ + 10 H₂ = 20.
example : (2 : ℚ) ^ 4 * (harmonic 5 - 2 * invPowTwoSum 5 + centralBinomWeightedSum 2) = 20 := by
  calc
    _ = ∑ i ∈ Finset.range 3, (Nat.choose 5 i : ℚ) * harmonic i :=
      (sum_range_choose_two_mul_sub_one_mul_harmonic 3 (by decide)).symm
    _ = 20 := by norm_num [Finset.sum_range_succ, Nat.choose, harmonic_succ]

-- At the smallest positive index the sum is 2, including a central correction of 1.
example : (∑ i ∈ Finset.range 2, (Nat.choose 2 i : ℚ) * harmonic i) = 2 := by
  rw [sum_range_choose_two_mul_mul_harmonic 1 (by decide)]
  have h : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  norm_num [invPowTwoSum, centralBinomWeightedSum, h, harmonic_succ, Nat.choose]

-- At n = 2 the central correction is 9/2 and the half-row sums to 13.
example : (2 : ℚ) ^ 3 * (harmonic 4 - 2 * invPowTwoSum 4 + centralBinomWeightedSum 2) +
    9 / 2 = 13 := by
  have h := (sum_range_choose_two_mul_mul_harmonic 2 (by decide)).symm
  norm_num [Finset.sum_range_succ, Nat.choose, harmonic_succ] at h ⊢
  exact h
