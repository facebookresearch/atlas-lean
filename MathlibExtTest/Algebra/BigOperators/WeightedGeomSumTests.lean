/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.BigOperators.WeightedGeomSum
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt

/-- The empty partial sum: the closed form gives `1 - 1 / 2 ^ 0 = 0`. -/
example : ∑ h ∈ Finset.range 0, (h : ℝ) / 2 ^ (h + 1) = 0 := by
  rw [sum_range_div_two_pow_succ_eq]
  norm_num

/-- Three terms: `0 + 1 / 4 + 2 / 8 = 1 / 2`, which is `1 - 4 / 2 ^ 3`. -/
example : ∑ h ∈ Finset.range 3, (h : ℝ) / 2 ^ (h + 1) = 1 / 2 := by
  rw [sum_range_div_two_pow_succ_eq]
  norm_num

/-- The partial sum at `k = 2` is `1 / 4`, below the bound `1`. -/
example : ∑ h ∈ Finset.range 2, (h : ℝ) / 2 ^ (h + 1) ≤ 1 :=
  sum_range_div_two_pow_succ_le_one 2

/-- With `n = 0` the scaled sum is empty and the bound reads `0 ≤ 0`. -/
example : ∑ h ∈ Finset.range 0, (((0 : ℕ) : ℝ) / 2 ^ (h + 1)) * h ≤ ((0 : ℕ) : ℝ) :=
  sum_range_div_two_pow_succ_mul_le 0

end
