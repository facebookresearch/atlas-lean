/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.NewtonMinimization
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace MathlibExt.Analysis.Convex.NewtonMinimization

-- The Taylor bound is sharp for `G x = x²`, whose derivative `2x` is `2`-Lipschitz:
-- `(x + d)² - x² - 2 x d = d²`.
example (x d : ℝ) : |(x + d) ^ 2 - x ^ 2 - 2 * x * d| ≤ 2 / 2 * |d| ^ 2 := by
  have hG : ∀ y : ℝ, HasFDerivAt (fun t : ℝ => t ^ 2)
      ((2 * y) • ContinuousLinearMap.id ℝ ℝ) y := by
    intro y
    simpa [pow_one] using (hasFDerivAt_id (𝕜 := ℝ) y).pow 2
  have hL : ∀ y y' : ℝ, ‖(2 * y) • ContinuousLinearMap.id ℝ ℝ -
      (2 * y') • ContinuousLinearMap.id ℝ ℝ‖ ≤ 2 * ‖y - y'‖ := by
    intro y y'
    have hsub : (2 * y) • ContinuousLinearMap.id ℝ ℝ - (2 * y') • ContinuousLinearMap.id ℝ ℝ =
        (2 * y - 2 * y') • ContinuousLinearMap.id ℝ ℝ := (sub_smul _ _ _).symm
    rw [hsub, norm_smul, ContinuousLinearMap.norm_id, mul_one, ← mul_sub, norm_mul]
    simp
  have := norm_sub_sub_le_of_lipschitz_fderiv hG hL x d
  simpa [Real.norm_eq_abs, smul_eq_mul, mul_assoc] using this

private noncomputable def q : ℝ → ℝ := fun x => (2 : ℝ)⁻¹ * x ^ 2

private theorem gradient_q : gradient q = id := by
  funext x
  have h : HasDerivAt q x x := by
    have := (hasDerivAt_pow 2 x).const_mul (2⁻¹ : ℝ)
    unfold q
    convert this using 1
    norm_num; ring
  rw [gradient_eq_deriv', h.deriv]
  rfl

-- For the quadratic `x² / 2`, whose Hessian is constant (`L = 0`, `m = 1`), one Newton step
-- from any point lands on a stationary point.
example (x : ℝ) : gradient q (x + -x) = 0 := by
  have hH : ∀ y, HasFDerivAt (gradient q) (ContinuousLinearMap.id ℝ ℝ) y := by
    intro y; rw [gradient_q]; exact hasFDerivAt_id y
  have h := norm_gradient_newton_step_le (L := 0) (m := 1) le_rfl one_pos hH
    (fun y y' => by simp) (x := x) (Δ := -x) (fun v => by simp)
    (by simp [gradient_q])
  simpa using h

end MathlibExt.Analysis.Convex.NewtonMinimization
