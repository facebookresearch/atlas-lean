/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.HopfUmlaufsatz
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.TwoDim

/-! # Tests for `MathlibExt.Geometry.HopfUmlaufsatz` -/

namespace MathlibExtTest.HopfUmlaufsatz

open Complex MathlibExt.Geometry.HopfUmlaufsatzWanted.Geometry.HopfUmlaufsatz

-- Test section: the definitions. The period is `2π` and the determinant of the standard basis
-- is `1`.
example : period = 2 * Real.pi := rfl

example : det2 !₂[1, 0] !₂[0, 1] = 1 := by simp [det2]

-- Test section: the unit circle `t ↦ (cos t, sin t)`, traversed counterclockwise, satisfies the
-- hypotheses of `hopf_umlaufsatz` with the tangent angle `t ↦ t + π / 2`, so they are not
-- vacuous; its total curvature is `2π`, computed directly and by the theorem.

/-- The counterclockwise unit circle, as a curve in the plane. -/
private noncomputable def circle (t : ℝ) : Plane :=
  orthonormalBasisOneI.repr (exp (t * I))

private theorem circle_apply_zero (t : ℝ) : circle t 0 = Real.cos t := by
  simp [circle, orthonormalBasisOneI_repr_apply, exp_ofReal_mul_I_re]

private theorem circle_apply_one (t : ℝ) : circle t 1 = Real.sin t := by
  simp [circle, orthonormalBasisOneI_repr_apply, exp_ofReal_mul_I_im]

private theorem hasDerivAt_circle (t : ℝ) :
    HasDerivAt circle (orthonormalBasisOneI.repr (exp (t * I) * I)) t := by
  have h : HasDerivAt (fun s : ℝ => exp (s * I)) (exp (t * I) * (1 * I)) t :=
    (((hasDerivAt_id t).ofReal_comp).mul_const I).cexp
  rw [one_mul] at h
  exact (orthonormalBasisOneI.repr.hasFDerivAt (x := exp (t * I))).comp_hasDerivAt t h

private theorem velocity_circle (t : ℝ) :
    velocity circle t = !₂[Real.cos (t + Real.pi / 2), Real.sin (t + Real.pi / 2)] := by
  rw [velocity, (hasDerivAt_circle t).deriv, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ext i
  fin_cases i <;> simp [orthonormalBasisOneI_repr_apply, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im]

private theorem isPositiveSimpleClosedUnitSpeedCurve_circle :
    IsPositiveSimpleClosedUnitSpeedCurve circle where
  smooth := orthonormalBasisOneI.repr.contDiff.comp
    ((Complex.contDiff_exp (𝕜 := ℝ)).comp (ofRealCLM.contDiff.mul contDiff_const))
  periodic t := by
    simp only [circle, period]
    push_cast
    rw [add_mul, exp_add, exp_two_pi_mul_I, mul_one]
  injective_on_period s hs t ht hst := by
    have h := orthonormalBasisOneI.repr.injective hst
    rw [← Circle.coe_exp, ← Circle.coe_exp, Circle.coe_inj] at h
    exact Circle.exp_injOn_Ico (by simp [period]) hs ht h
  unit_speed t := by
    rw [velocity, (hasDerivAt_circle t).deriv, LinearIsometryEquiv.norm_map, norm_mul,
      norm_exp_ofReal_mul_I, norm_I, mul_one]
  positive_orientation := by
    have h : ∀ t, det2 (circle t) (velocity circle t) = 1 := fun t => by
      rw [velocity_circle, det2, circle_apply_zero, circle_apply_one, Real.cos_add_pi_div_two,
        Real.sin_add_pi_div_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [Real.sin_sq_add_cos_sq t]
    simp only [signedArea, h, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero,
      period]
    positivity

private theorem isTangentAngleLift_circle :
    IsTangentAngleLift circle fun t => t + Real.pi / 2 where
  smooth := contDiff_id.add contDiff_const
  velocity_eq := velocity_circle

example : totalCurvature (fun t => t + Real.pi / 2) = 2 * Real.pi :=
  hopf_umlaufsatz isPositiveSimpleClosedUnitSpeedCurve_circle isTangentAngleLift_circle

-- The same value, computed directly: the signed curvature of the circle is `1`.
example : totalCurvature (fun t => t + Real.pi / 2) = 2 * Real.pi := by
  have h : ∀ t, signedCurvature (fun t => t + Real.pi / 2) t = 1 := fun t => by
    simp [signedCurvature]
  simp [totalCurvature, h, period]

end MathlibExtTest.HopfUmlaufsatz
