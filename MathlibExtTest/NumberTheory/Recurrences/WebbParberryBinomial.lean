/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.WebbParberryBinomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- At `m = 1`, `n = 5`, the exponent is negative and two summands contribute.
example : (∑ j ∈ Icc 1 2, (j.choose 1 : ℚ) * (Nat.choose 5 (2 * j + 1) : ℚ)) = 12 := by
  have h := choose_sub_sub_one_eq_two_zpow_mul_sum (m := 1) (n := 5) (by decide)
  change (3 : ℚ) = (2 : ℚ) ^ (-2 : ℤ) *
    ∑ j ∈ Icc 1 2, (j.choose 1 : ℚ) * (Nat.choose 5 (2 * j + 1) : ℚ) at h
  norm_num at h
  simp only [Nat.choose_one_right]
  linarith only [h]

-- The original range `m < n` also permits an empty summation interval.
example : ((4 - 3 - 1 : ℕ).choose 3 : ℚ) = 0 := by
  have h := choose_sub_sub_one_eq_two_zpow_mul_sum (m := 3) (n := 4) (by decide)
  have hempty : Icc 3 ((4 - 1) / 2) = (∅ : Finset ℕ) := by decide
  rw [hempty, sum_empty, mul_zero] at h
  exact h
