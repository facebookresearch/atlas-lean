/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.GcdSumMeanSquare

open MetaMathlibExt Complex

-- The value at zero agrees with the convention in the definition.
example : gcdSumMean 0 = 0 := by simp [gcdSumMean]

-- A repeated prime divisor contributes twice to the mean.
example : gcdSumMean 4 = 2 := by
  rw [gcdSumMean, show Finset.Icc 1 4 = {1, 2, 3, 4} by decide]
  norm_num

-- The same correction series converges inside the strip and gives the identity to its right.
example : ∃ h : ℕ → ℂ, LSeriesSummable h (1 / 4 + I) ∧
    LSeries (fun n => ((gcdSumMean n ^ 2 : ℝ) : ℂ)) (2 + I) =
      riemannZeta (2 + I) ^ 4 / riemannZeta (2 * (2 + I)) * LSeries h (2 + I) := by
  obtain ⟨h, hsum, heq⟩ := LSeries_gcdSumMean_sq_eq_riemannZeta_pow_four_div
  exact ⟨h, hsum _ (by norm_num), heq _ (by norm_num)⟩
