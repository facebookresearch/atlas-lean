/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.SpecificLimits.PowerSeriesCoeffEqOfAgreeOnReciprocals
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Tests for coefficient uniqueness from reciprocal evaluations -/

open MathlibExt.Analysis.SpecificLimits.PowerSeriesCoeffEqOfAgreeOnReciprocalsWanted

-- Reciprocal evaluations of the alternating geometric series determine all its coefficients.
example (b : ℕ → ℝ) (hb : ∀ x : ℝ, |x| < 1 → Summable (fun k : ℕ => b k * x ^ k))
    (h : ∀ n : ℕ,
      (∑' k : ℕ, b k * ((1 : ℝ) / (n + 2)) ^ k) = (1 + (1 : ℝ) / (n + 2))⁻¹) :
    ∀ k : ℕ, b k = (-1 : ℝ) ^ k := by
  refine coeff_eq_of_tsum_eq_on_inv_nat_add_two b (fun k ↦ (-1 : ℝ) ^ k) hb ?_ ?_
  · intro x hx
    simp only [← mul_pow, neg_one_mul]
    exact summable_geometric_of_norm_lt_one (by simpa only [norm_neg, Real.norm_eq_abs] using hx)
  · intro n
    let x : ℝ := 1 / (n + 2)
    have hx : ‖-x‖ < 1 := by
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by dsimp [x]; positivity)]
      dsimp [x]
      rw [div_lt_one (by positivity)]
      exact (by norm_num : (1 : ℝ) < 2).trans_le (le_add_of_nonneg_left (Nat.cast_nonneg n))
    change (∑' k, b k * x ^ k) = ∑' k, (-1 : ℝ) ^ k * x ^ k
    rw [h n]
    simp only [← mul_pow, neg_one_mul, tsum_geometric_of_norm_lt_one hx, sub_neg_eq_add, x]
