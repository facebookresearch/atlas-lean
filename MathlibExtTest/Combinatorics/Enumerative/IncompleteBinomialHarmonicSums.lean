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

-- The auxiliary sums start with an empty interval and include the upper endpoint.
example : invPowTwoSum 0 = 0 ∧ centralBinomWeightedSum 0 = 0 := by decide
example : invPowTwoSum 2 = 5 / 8 ∧ centralBinomWeightedSum 2 = 11 / 32 := by
  have h : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  norm_num [invPowTwoSum, centralBinomWeightedSum, h, Nat.choose]
