/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.SecondOrderCondition
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow

namespace MathlibExt.Analysis.Convex.SecondOrderCondition

/-- The derivative `y ↦ 2 y` of `y ↦ y²`, as a continuous linear map. -/
private noncomputable def sq' (y : ℝ) : ℝ →L[ℝ] ℝ := y • ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)

/-- The constant second derivative of `y ↦ y²`. -/
private noncomputable def sq'' (_ : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)

private theorem hsq (y : ℝ) : HasFDerivAt (fun x : ℝ => x ^ 2) (sq' y) y := by
  have h := (hasFDerivAt_id (𝕜 := ℝ) y).pow 2
  refine h.congr_fderiv ?_
  change _ = y • ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
  rw [smul_smul]
  congr 1
  simp
  ring

private theorem hsq' (y : ℝ) : HasFDerivAt sq' (sq'' y) y := by
  have h := (hasFDerivAt_id (𝕜 := ℝ) y).smul_const ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
  exact h

-- `y ↦ y²` is convex, from its Hessian `2 ≥ 0`.
example : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
  convexOn_of_hessian_nonneg isOpen_univ convex_univ (fun y _ => hsq y) (fun y _ => hsq' y)
    (fun y _ v => by
      change 0 ≤ ((ContinuousLinearMap.id ℝ ℝ).smulRight ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
        v) v
      simp
      nlinarith [sq_nonneg v])

-- `y ↦ -y²` is not convex: its Hessian `-2` is negative.
example : ¬ ConvexOn ℝ Set.univ (fun x : ℝ => -x ^ 2) := by
  intro h
  have hneg := hessian_nonneg_of_convexOn (f' := fun y => -sq' y) (f'' := fun y => -sq'' y)
    isOpen_univ h (fun z _ => (hsq z).neg) (Set.mem_univ 0) (hsq' 0).neg 1
  change 0 ≤ (-((ContinuousLinearMap.id ℝ ℝ).smulRight ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ))
    1) 1 at hneg
  simp at hneg
  norm_num at hneg

end MathlibExt.Analysis.Convex.SecondOrderCondition
