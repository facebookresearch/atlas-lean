/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Operator.LinearSystemPerturbation

@[expose] public section

open MathlibExt.Analysis.Normed.Operator.LinearSystemPerturbation

namespace MathlibExtTest.Analysis.Normed.Operator.LinearSystemPerturbation

/-- In `ℝ` with `A = 2` and `E = 1/2`: `‖E‖ ‖A⁻¹‖ = 1/4 < 1`, `A - E = 3/2` is invertible and
`(A - E)⁻¹ = 2/3 ≤ (1/2) / (1 - 1/4) = 2/3` (the bound is attained). -/
example : ‖Ring.inverse (((Units.mk0 (2 : ℝ) two_ne_zero) : ℝ) - 1 / 2)‖ ≤
    ‖((Units.mk0 (2 : ℝ) two_ne_zero)⁻¹ : ℝ)‖ /
      (1 - ‖(1 / 2 : ℝ)‖ * ‖((Units.mk0 (2 : ℝ) two_ne_zero)⁻¹ : ℝ)‖) :=
  norm_inverse_sub_le _ _ (by norm_num)

example : IsUnit (((Units.mk0 (2 : ℝ) two_ne_zero) : ℝ) - 1 / 2) :=
  isUnit_sub _ _ (by norm_num)

/-- `κ(A) ≥ 1` for the unit `2 ∈ ℝ`: `2 · (1/2) = 1`. -/
example : 1 ≤ ‖((Units.mk0 (2 : ℝ) two_ne_zero) : ℝ)‖ * ‖((Units.mk0 (2 : ℝ) two_ne_zero)⁻¹ : ℝ)‖ :=
  one_le_norm_mul_norm_inv _

/-- The hypotheses of the linear-system bound are jointly satisfiable, and the bound is attained:
on `ℝ`, `A = 1`, `E = (1/2) • id`, `x = b = 1`, `δx = 1`, `f = 0`, since
`(1 - E)(1 + 1) = 1`; then `‖δx‖ / ‖x‖ = 1 = 1 / (1 - 1/2) · (0 + 1/2)`. -/
example : ‖(1 : ℝ)‖ / ‖(1 : ℝ)‖ ≤
    ‖((1 : (ℝ →L[ℝ] ℝ)ˣ) : ℝ →L[ℝ] ℝ)‖ * ‖(↑(1 : (ℝ →L[ℝ] ℝ)ˣ)⁻¹ : ℝ →L[ℝ] ℝ)‖ /
        (1 - ‖(1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ *
          ‖(↑(1 : (ℝ →L[ℝ] ℝ)ˣ)⁻¹ : ℝ →L[ℝ] ℝ)‖) *
      (‖(0 : ℝ)‖ / ‖(1 : ℝ)‖ +
        ‖(1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ / ‖((1 : (ℝ →L[ℝ] ℝ)ˣ) : ℝ →L[ℝ] ℝ)‖) := by
  refine norm_sub_div_norm_le (1 : (ℝ →L[ℝ] ℝ)ˣ) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    (x := 1) (δx := 1) (b := 1) (f := 0) (by simp) one_ne_zero ?_ ?_
  · simp; norm_num
  · rw [norm_smul, ContinuousLinearMap.norm_id]; simp; norm_num

end MathlibExtTest.Analysis.Normed.Operator.LinearSystemPerturbation
