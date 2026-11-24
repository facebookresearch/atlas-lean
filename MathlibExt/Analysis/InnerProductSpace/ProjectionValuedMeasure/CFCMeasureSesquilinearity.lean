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
# Sesquilinearity of the actual normal-CFC regular coefficient measures

These strict laws serve the bounded coefficient-operator construction needed
by resolutionOfIdentity and its Borel functional calculus. They use the actual
regular complex-Riesz measure and its existing strict linear equivalence with
the continuous dual, without any PVM, norm, field or desired-output premise.
The original complete H, normal T, coefficient orientation and scalar action
are retained. No terminal textbook theorem is proved or used here.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped CStarAlgebra InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The first coefficient vector is additive for the actual regular complex measure. -/
theorem normalCFCCoefficientMeasure_add_left (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g₁ g₂ h : H) :
    normalCFCCoefficientMeasure T hT (g₁ + g₂) h =
      normalCFCCoefficientMeasure T hT g₁ h + normalCFCCoefficientMeasure T hT g₂ h := by
  apply (MathlibExt.MeasureTheory.complexIntegralEquiv (X := spectrum ℂ T)).injective
  rw [map_add]
  simp only [MathlibExt.MeasureTheory.complexIntegralEquiv_apply,
    normalCFCCoefficientMeasure, MathlibExt.MeasureTheory.complexIntegralDual_complexRieszMeasure]
  ext f
  simp only [normalCFCCoefficientFunctional_apply, add_apply,
    map_add, inner_add_right]

/-- The first coefficient vector is complex-linear, with the original scalar action. -/
theorem normalCFCCoefficientMeasure_smul_left (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (c : ℂ) (g h : H) :
    normalCFCCoefficientMeasure T hT (c • g) h =
      c • normalCFCCoefficientMeasure T hT g h := by
  apply (MathlibExt.MeasureTheory.complexIntegralEquiv (X := spectrum ℂ T)).injective
  rw [map_smul]
  simp only [MathlibExt.MeasureTheory.complexIntegralEquiv_apply,
    normalCFCCoefficientMeasure, MathlibExt.MeasureTheory.complexIntegralDual_complexRieszMeasure]
  ext f
  simp only [normalCFCCoefficientFunctional_apply, smul_apply,
    map_smul, inner_smul_right, smul_eq_mul]

/-- The second coefficient vector is additive for the same measure. -/
theorem normalCFCCoefficientMeasure_add_right (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h₁ h₂ : H) :
    normalCFCCoefficientMeasure T hT g (h₁ + h₂) =
      normalCFCCoefficientMeasure T hT g h₁ + normalCFCCoefficientMeasure T hT g h₂ := by
  apply (MathlibExt.MeasureTheory.complexIntegralEquiv (X := spectrum ℂ T)).injective
  rw [map_add]
  simp only [MathlibExt.MeasureTheory.complexIntegralEquiv_apply,
    normalCFCCoefficientMeasure, MathlibExt.MeasureTheory.complexIntegralDual_complexRieszMeasure]
  ext f
  simp only [normalCFCCoefficientFunctional_apply, add_apply,
    inner_add_left]

/-- The second coefficient vector is conjugate-linear, in the scalarMeasure g h orientation. -/
theorem normalCFCCoefficientMeasure_smul_right (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (c : ℂ) (g h : H) :
    normalCFCCoefficientMeasure T hT g (c • h) =
      star c • normalCFCCoefficientMeasure T hT g h := by
  apply (MathlibExt.MeasureTheory.complexIntegralEquiv (X := spectrum ℂ T)).injective
  rw [map_smul]
  simp only [MathlibExt.MeasureTheory.complexIntegralEquiv_apply,
    normalCFCCoefficientMeasure, MathlibExt.MeasureTheory.complexIntegralDual_complexRieszMeasure]
  ext f
  simp only [normalCFCCoefficientFunctional_apply, smul_apply,
    inner_smul_left, smul_eq_mul, starRingEnd_apply]

/-- Zero in the first vector gives the actual zero regular complex measure. -/
theorem normalCFCCoefficientMeasure_zero_left (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (h : H) :
    normalCFCCoefficientMeasure T hT 0 h = 0 := by
  apply (MathlibExt.MeasureTheory.complexIntegralEquiv (X := spectrum ℂ T)).injective
  rw [map_zero]
  simp only [MathlibExt.MeasureTheory.complexIntegralEquiv_apply,
    normalCFCCoefficientMeasure, MathlibExt.MeasureTheory.complexIntegralDual_complexRieszMeasure]
  ext f
  simp only [normalCFCCoefficientFunctional_apply, zero_apply,
    map_zero, inner_zero_right]

/-- Zero in the second vector gives the actual zero regular complex measure. -/
theorem normalCFCCoefficientMeasure_zero_right (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) :
    normalCFCCoefficientMeasure T hT g 0 = 0 := by
  apply (MathlibExt.MeasureTheory.complexIntegralEquiv (X := spectrum ℂ T)).injective
  rw [map_zero]
  simp only [MathlibExt.MeasureTheory.complexIntegralEquiv_apply,
    normalCFCCoefficientMeasure, MathlibExt.MeasureTheory.complexIntegralDual_complexRieszMeasure]
  ext f
  simp only [normalCFCCoefficientFunctional_apply, zero_apply,
    inner_zero_left]

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
