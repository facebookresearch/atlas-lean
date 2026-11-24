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
public import MathlibExt.MeasureTheory.Integral.RieszMarkovKakutani.CompactReal
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Positive diagonal measures of the actual normal CFC coefficients

The actual normal T and original vector g determine a positive finite regular
measure on the original spectrum. Its complexification is the same strict
complex-Riesz diagonal coefficient, and its mass is the original squared
Hilbert norm. These facts serve the missing canonical PVM/resolutionOfIdentity
constructor and BFC DATA; no positivity, mass, regularity, representation or
PVM/output certificate is an input. The numbered source spectral proofs stay open.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped CStarAlgebra InnerProductSpace ENNReal

namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
open MathlibExt.MeasureTheory
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real restriction of the actual original diagonal CFC functional. -/
def normalCFCDiagonalRealFunctional (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    StrongDual ℝ C(spectrum ℂ T, ℝ) :=
  complexDualRealRestriction (normalCFCCoefficientFunctional T hT g g)

/-- It is the real part of the same original CFC coefficient. -/
theorem normalCFCDiagonalRealFunctional_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) (f : C(spectrum ℂ T, ℝ)) :
    normalCFCDiagonalRealFunctional T hT g f =
      (⟪g, cfcHom hT (realContinuousMapCLM f) g⟫_ℂ).re := rfl

private theorem real_cfc_isSelfAdjoint (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (f : C(spectrum ℂ T, ℝ)) : IsSelfAdjoint (cfcHom hT (realContinuousMapCLM f)) := by
  have hs : star (realContinuousMapCLM f) = realContinuousMapCLM f := by
    ext x
    simp only [ContinuousMap.star_apply, realContinuousMapCLM_apply, Complex.star_def,
      Complex.conj_ofReal]
  change star (cfcHom hT (realContinuousMapCLM f)) = cfcHom hT (realContinuousMapCLM f)
  rw [← map_star, hs]

/-- A real-valued continuous input gives a real diagonal coefficient. -/
theorem normalCFCCoefficientFunctional_diagonal_im_eq_zero (T : H →L[ℂ] H)
    (hT : IsStarNormal T) (g : H) (f : C(spectrum ℂ T, ℝ)) :
    (normalCFCCoefficientFunctional T hT g g (realContinuousMapCLM f)).im = 0 := by
  rw [normalCFCCoefficientFunctional_apply]
  simpa only [RCLike.im_eq_complex_im, ContinuousLinearMap.coe_coe] using
    (real_cfc_isSelfAdjoint T hT f).isSymmetric.im_inner_self_apply g

private theorem real_cfc_isPositive (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (f : C(spectrum ℂ T, ℝ)) (hf : 0 ≤ f) :
    (cfcHom hT (realContinuousMapCLM f)).IsPositive := by
  let r : C(spectrum ℂ T, ℝ) := ⟨fun x => Real.sqrt (f x), Real.continuous_sqrt.comp f.continuous⟩
  let q : C(spectrum ℂ T, ℂ) := realContinuousMapCLM r
  have hfactor : star q * q = realContinuousMapCLM f := by
    ext x
    simp only [q, ContinuousMap.mul_apply, ContinuousMap.star_apply, realContinuousMapCLM_apply]
    change star (Real.sqrt (f x) : ℂ) * (Real.sqrt (f x) : ℂ) = (f x : ℂ)
    have hr : star (Real.sqrt (f x) : ℂ) = (Real.sqrt (f x) : ℂ) := by simp
    rw [hr, ← Complex.ofReal_mul]
    exact congrArg Complex.ofReal (Real.mul_self_sqrt (ContinuousMap.le_def.mp hf x))
  let Q : H →L[ℂ] H := cfcHom hT q
  have hQ : (star Q * Q).IsPositive := by
    change (Q.adjoint.comp Q).IsPositive
    exact ContinuousLinearMap.isPositive_adjoint_comp_self Q
  have heq : cfcHom hT (realContinuousMapCLM f) = star Q * Q := by
    rw [← hfactor, map_mul, map_star]
  rw [heq]
  exact hQ

/-- Positivity follows from the actual CFC square-root factor and Gram positivity. -/
theorem normalCFCDiagonalRealFunctional_nonneg (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) (f : C(spectrum ℂ T, ℝ)) (hf : 0 ≤ f) :
    0 ≤ normalCFCDiagonalRealFunctional T hT g f := by
  rw [normalCFCDiagonalRealFunctional_apply]
  simpa only [RCLike.re_eq_complex_re] using
    (real_cfc_isPositive T hT f hf).re_inner_nonneg_right g

/-- The actual positive compact-real functional, with proved order compatibility. -/
def normalCFCDiagonalPositiveFunctional (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    C(spectrum ℂ T, ℝ) →P[ℝ] ℝ where
  toPositiveLinearMap :=
    { toLinearMap := (normalCFCDiagonalRealFunctional T hT g).toLinearMap
      monotone' := by
        intro f k hfk
        have h := normalCFCDiagonalRealFunctional_nonneg T hT g (k - f) (sub_nonneg.mpr hfk)
        rw [map_sub] at h
        exact sub_nonneg.mp h }
  cont := (normalCFCDiagonalRealFunctional T hT g).cont

/-- Its value is still the original real diagonal coefficient. -/
theorem normalCFCDiagonalPositiveFunctional_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) (f : C(spectrum ℂ T, ℝ)) :
    normalCFCDiagonalPositiveFunctional T hT g f = normalCFCDiagonalRealFunctional T hT g f := rfl

/-- Positive compact-real Riesz representation computes the original diagonal measure. -/
def normalCFCDiagonalMeasure (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    Measure (spectrum ℂ T) :=
  continuousRieszMeasure (normalCFCDiagonalPositiveFunctional T hT g)

/-- This exact positive Riesz measure is finite. -/
instance normalCFCDiagonalMeasure_finite (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    IsFiniteMeasure (normalCFCDiagonalMeasure T hT g) :=
  continuousRieszMeasure_finite (normalCFCDiagonalPositiveFunctional T hT g)

/-- This exact positive Riesz measure is regular. -/
instance normalCFCDiagonalMeasure_regular (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    (normalCFCDiagonalMeasure T hT g).Regular :=
  continuousRieszMeasure_regular (normalCFCDiagonalPositiveFunctional T hT g)

/-- The positive measure represents every original continuous real diagonal value. -/
theorem normalCFCDiagonalMeasure_represents (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) (f : C(spectrum ℂ T, ℝ)) :
    ∫ x, f x ∂(normalCFCDiagonalMeasure T hT g) = normalCFCDiagonalRealFunctional T hT g f :=
  integral_continuousRieszMeasure (normalCFCDiagonalPositiveFunctional T hT g) f

/-- The mass is the original squared vector norm, including zero H/empty spectrum. -/
theorem normalCFCDiagonalMeasure_real_univ (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    (normalCFCDiagonalMeasure T hT g).real univ = ‖g‖ ^ 2 := by
  rw [normalCFCDiagonalMeasure, continuousRieszMeasure_real_univ]
  change normalCFCDiagonalRealFunctional T hT g 1 = ‖g‖ ^ 2
  rw [normalCFCDiagonalRealFunctional_apply]
  have h1 : realContinuousMapCLM (1 : C(spectrum ℂ T, ℝ)) = 1 := by
    ext x
    simp only [realContinuousMapCLM_apply, ContinuousMap.one_apply, Complex.ofReal_one]
  rw [h1, map_one]
  simpa only [_root_.one_apply_eq_self, RCLike.re_eq_complex_re] using
    inner_self_eq_norm_sq (𝕜 := ℂ) g

private def diagonalRegularSignedMeasure (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    RegularSignedMeasure (spectrum ℂ T) :=
  ⟨(normalCFCDiagonalMeasure T hT g).toSignedMeasure, by
    change (((normalCFCDiagonalMeasure T hT g).toSignedMeasure).totalVariation).Regular
    rw [SignedMeasure.totalVariation_eq_variation, Measure.variation_toSignedMeasure]
    exact normalCFCDiagonalMeasure_regular T hT g⟩

private theorem signed_diagonal_represents (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    RegularSignedMeasure.signedIntegralDual (diagonalRegularSignedMeasure T hT g) =
      normalCFCDiagonalRealFunctional T hT g := by
  apply ContinuousLinearMap.ext
  intro f
  rw [RegularSignedMeasure.signedIntegralDual_apply]
  change (∫ᵛ x, f x ∂<•(normalCFCDiagonalMeasure T hT g).toSignedMeasure) = _
  rw [_root_.MeasureTheory.VectorMeasure.integral_toSignedMeasure]
  exact normalCFCDiagonalMeasure_represents T hT g f

/-- The complex-Riesz diagonal is exactly the complexification of the computed positive measure. -/
theorem normalCFCCoefficientMeasure_diagonal (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    (normalCFCCoefficientMeasure T hT g g : ComplexMeasure (spectrum ℂ T)) =
      ((normalCFCDiagonalMeasure T hT g).toSignedMeasure).toComplexMeasure 0 := by
  let L := normalCFCCoefficientFunctional T hT g g
  have hre : signedRieszMeasure (complexDualRealRestriction L) =
      diagonalRegularSignedMeasure T hT g :=
    signedRieszMeasure_unique _ _ (signed_diagonal_represents T hT g)
  have him : complexDualImagRestriction L = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change (normalCFCCoefficientFunctional T hT g g (realContinuousMapCLM f)).im = 0
    exact normalCFCCoefficientFunctional_diagonal_im_eq_zero T hT g f
  have hz : signedRieszMeasure (complexDualImagRestriction L) = 0 := by
    rw [him]
    simpa only [signedIntegralEquiv_symm_apply] using
      (signedIntegralEquiv (X := spectrum ℂ T)).symm.map_zero
  change SignedMeasure.toComplexMeasure
    (signedRieszMeasure (complexDualRealRestriction L) : SignedMeasure (spectrum ℂ T))
    (signedRieszMeasure (complexDualImagRestriction L) : SignedMeasure (spectrum ℂ T)) = _
  rw [hre, hz]
  rfl


/-- Every measurable diagonal coefficient value is the computed positive mass. -/
theorem normalCFCCoefficientMeasure_diagonal_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    (normalCFCCoefficientMeasure T hT g g : ComplexMeasure (spectrum ℂ T)) s =
      ((normalCFCDiagonalMeasure T hT g).real s : ℂ) := by
  rw [normalCFCCoefficientMeasure_diagonal, SignedMeasure.toComplexMeasure_apply]
  simp only [Measure.toSignedMeasure_apply_measurable hs, _root_.zero_apply]
  apply Complex.ext <;>
    simp only [Complex.ofReal_re, Complex.ofReal_im]

/-- The complex diagonal mass is the original squared vector norm. -/
theorem normalCFCCoefficientMeasure_diagonal_univ (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) :
    (normalCFCCoefficientMeasure T hT g g : ComplexMeasure (spectrum ℂ T)) univ =
      (‖g‖ ^ 2 : ℝ) := by
  rw [normalCFCCoefficientMeasure_diagonal_apply T hT g univ MeasurableSet.univ,
    normalCFCDiagonalMeasure_real_univ]

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

end
