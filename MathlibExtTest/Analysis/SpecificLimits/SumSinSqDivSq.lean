/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.SumSinSqDivSq

/-! # Tests for `MathlibExt.Analysis.SpecificLimits.SumSinSqDivSq` -/

namespace MathlibExtTest.Analysis.SpecificLimits.SumSinSqDivSq

open MathlibExt.Analysis.SpecificLimits.SumSinSqDivSqWanted

-- At `δ = π / 2` the series sums to `π / 4`.
example :
    (∑' n : ℕ, Real.sin ((n + 1 : ℕ) * (Real.pi / 2)) ^ 2 /
      ((n + 1 : ℕ) ^ 2 * (Real.pi / 2))) = Real.pi / 4 := by
  rw [tsum_sin_sq_mul_div_sq_mul (by positivity) (by linarith [Real.pi_pos])]
  ring

-- At `δ = 2π / 3` the series sums to `π / 6`.
example :
    (∑' n : ℕ, Real.sin ((n + 1 : ℕ) * (2 * Real.pi / 3)) ^ 2 /
      ((n + 1 : ℕ) ^ 2 * (2 * Real.pi / 3))) = Real.pi / 6 := by
  rw [tsum_sin_sq_mul_div_sq_mul (by positivity) (by linarith [Real.pi_pos])]
  ring

-- Multiplying by `δ`: `∑ sin² ((n + 1) δ) / (n + 1)² = δ (π - δ) / 2` for `0 < δ < π`.
example {δ : ℝ} (hδ0 : 0 < δ) (hδpi : δ < Real.pi) :
    ∑' n : ℕ, Real.sin ((n + 1 : ℕ) * δ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 =
      δ * (Real.pi - δ) / 2 := by
  have h := tsum_sin_sq_mul_div_sq_mul hδ0 hδpi
  simp_rw [← div_div, tsum_div_const] at h
  rw [div_eq_iff hδ0.ne'] at h
  rw [h]
  ring

-- The hypothesis `0 < δ` cannot be dropped: at `δ = 0` every term is `0`, as `x / 0 = 0`,
-- while the right-hand side is `π / 2`.
example :
    (∑' n : ℕ, Real.sin ((n + 1 : ℕ) * (0 : ℝ)) ^ 2 / ((n + 1 : ℕ) ^ 2 * (0 : ℝ))) ≠
      (Real.pi - 0) / 2 := by
  simp only [mul_zero, div_zero, tsum_zero, sub_zero]
  exact (div_pos Real.pi_pos two_pos).ne

-- The hypothesis `δ < π` cannot be dropped: at `δ = 2π` every term vanishes, while the
-- right-hand side is `-π / 2`.
example :
    (∑' n : ℕ, Real.sin ((n + 1 : ℕ) * (2 * Real.pi)) ^ 2 /
      ((n + 1 : ℕ) ^ 2 * (2 * Real.pi))) ≠ (Real.pi - 2 * Real.pi) / 2 := by
  have h (n : ℕ) : Real.sin ((n + 1 : ℕ) * (2 * Real.pi)) = 0 := by
    simpa using Real.sin_add_nat_mul_two_pi 0 (n + 1)
  simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, tsum_zero]
  intro h'
  linarith [Real.pi_pos]

end MathlibExtTest.Analysis.SpecificLimits.SumSinSqDivSq
