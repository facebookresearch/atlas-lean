/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureCoefficients

/-!
# Actual continuous-CFC product identities for the regular coefficient measures

These strict identities serve the PVM intersection/projection construction
required by resolutionOfIdentity and Borel defining DATA. The continuous
integrands and original vectors are actual inputs; only cfcHom multiplication,
star and the existing adjoint identity are used. The actual regular measures
are identified by strict complex-Riesz uniqueness. No supplied PVM, weighted-
measure correctness, bound, form or output certificate is assumed. The
original complete H and normal T are retained, including zero H/empty spectrum.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped CStarAlgebra InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Acting on the first vector by the actual continuous CFC multiplies the continuous integrand. -/
theorem normalCFCCoefficientMeasure_cfc_mul_left (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (f q : C(spectrum ℂ T, ℂ)) :
    MathlibExt.MeasureTheory.complexIntegralDual
      (normalCFCCoefficientMeasure T hT (cfcHom hT f g) h) q =
    MathlibExt.MeasureTheory.complexIntegralDual (normalCFCCoefficientMeasure T hT g h) (q * f) := by
  rw [normalCFCCoefficientMeasure_represents, normalCFCCoefficientMeasure_represents, map_mul]
  rfl

/-- The original CFC star moves the continuous factor to the second coefficient vector. -/
theorem normalCFCCoefficientMeasure_cfc_star_mul_right (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (f q : C(spectrum ℂ T, ℂ)) :
    MathlibExt.MeasureTheory.complexIntegralDual
      (normalCFCCoefficientMeasure T hT g (cfcHom hT (star f) h)) q =
    MathlibExt.MeasureTheory.complexIntegralDual (normalCFCCoefficientMeasure T hT g h) (q * f) := by
  rw [normalCFCCoefficientMeasure_represents, normalCFCCoefficientMeasure_represents, map_star]
  change ⟪(cfcHom hT f).adjoint h, cfcHom hT q g⟫_ℂ =
    ⟪h, cfcHom hT (q * f) g⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left, mul_comm q f, map_mul]
  rfl

/-- Acting on the second vector inserts the conjugate continuous integrand. -/
theorem normalCFCCoefficientMeasure_cfc_mul_right (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (f q : C(spectrum ℂ T, ℂ)) :
    MathlibExt.MeasureTheory.complexIntegralDual
      (normalCFCCoefficientMeasure T hT g (cfcHom hT f h)) q =
    MathlibExt.MeasureTheory.complexIntegralDual (normalCFCCoefficientMeasure T hT g h) (q * star f) := by
  simpa only [star_star] using
    normalCFCCoefficientMeasure_cfc_star_mul_right T hT g h (star f) q

/-- Riesz uniqueness gives equality of the same actual regular complex coefficient measures. -/
theorem normalCFCCoefficientMeasure_cfc_balance (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (f : C(spectrum ℂ T, ℂ)) :
    normalCFCCoefficientMeasure T hT (cfcHom hT f g) h =
    normalCFCCoefficientMeasure T hT g (cfcHom hT (star f) h) := by
  apply MathlibExt.MeasureTheory.complexIntegralDual_injective
  ext q
  rw [normalCFCCoefficientMeasure_cfc_mul_left, normalCFCCoefficientMeasure_cfc_star_mul_right]

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
