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
# Positive diagonal CFC measures and their masses

For a normal operator `T` on a complete complex Hilbert space and vector `g`, the real
functional `f ↦ Re ⟨g,f(T)g⟩` on `C(σ_ℂ(T),ℝ)` is positive. It is represented by a finite
regular positive measure `ν_g`.

Its total mass is `ν_g(σ_ℂ(T))=‖g‖²`. The diagonal complex coefficient measure `μ_(g,g)` is the
complexification of `ν_g`, so for measurable `s`, `μ_(g,g)(s)=(ν_g.real(s) : ℂ)`. These
identities permit a zero vector or zero Hilbert space.
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

/-- **Real diagonal functional of continuous CFC.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. for `g ∈ H`, `normalCFCDiagonalRealFunctional T hT g : C(K,ℝ) →L[ℝ]
ℝ` sends a real-valued continuous `f` to `Re ⟨g,f(T)g⟩`, with `f` embedded in `C(K,ℂ)`. -/
def normalCFCDiagonalRealFunctional (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    StrongDual ℝ C(spectrum ℂ T, ℝ) :=
  complexDualRealRestriction (normalCFCCoefficientFunctional T hT g g)

/-- **Real value of a diagonal CFC functional.** Let `H` be a complete complex Hilbert space
and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. for `g ∈ H` and `f ∈ C(K,ℝ)`, `normalCFCDiagonalRealFunctional T hT
g f=Re ⟨g,f(T)g⟩`. -/
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

/-- **Reality of a real-valued diagonal CFC coefficient.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. for `g ∈ H` and `f ∈ C(K,ℝ)` viewed as complex-valued, `Im
⟨g,f(T)g⟩=0`. -/
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

/-- **Positivity of the real diagonal CFC functional.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. for `g ∈ H` and pointwise nonnegative `f ∈ C(K,ℝ)`,
`0≤normalCFCDiagonalRealFunctional T hT g f=Re ⟨g,f(T)g⟩`. -/
theorem normalCFCDiagonalRealFunctional_nonneg (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) (f : C(spectrum ℂ T, ℝ)) (hf : 0 ≤ f) :
    0 ≤ normalCFCDiagonalRealFunctional T hT g f := by
  rw [normalCFCDiagonalRealFunctional_apply]
  simpa only [RCLike.re_eq_complex_re] using
    (real_cfc_isPositive T hT f hf).re_inner_nonneg_right g

/-- **Positive real-linear diagonal functional.** Let `H` be a complete complex Hilbert space
and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. for `g ∈ H`, `normalCFCDiagonalPositiveFunctional T hT g` is the
positive real-linear functional `f ↦ Re ⟨g,f(T)g⟩` on `C(K,ℝ)`. -/
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

/-- **Value of the positive diagonal functional.** Let `H` be a complete complex Hilbert space
and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. for `g ∈ H` and `f ∈ C(K,ℝ)`, the positive functional has the same
value `Re ⟨g,f(T)g⟩` as `normalCFCDiagonalRealFunctional T hT g f`. -/
theorem normalCFCDiagonalPositiveFunctional_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) (f : C(spectrum ℂ T, ℝ)) :
    normalCFCDiagonalPositiveFunctional T hT g f = normalCFCDiagonalRealFunctional T hT g f := rfl

/-- **Positive Riesz measure of a diagonal CFC coefficient.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. for `g ∈ H`, `normalCFCDiagonalMeasure T hT g` is the
positive measure `ν_g` on `K` satisfying `∫ f dν_g=Re ⟨g,f(T)g⟩` for `f ∈ C(K,ℝ)`. -/
def normalCFCDiagonalMeasure (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    Measure (spectrum ℂ T) :=
  continuousRieszMeasure (normalCFCDiagonalPositiveFunctional T hT g)

/-- **Finite mass of a diagonal CFC measure.** Let `H` be a complete complex Hilbert space and
`T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. for `g ∈ H`, the positive measure `ν_g=normalCFCDiagonalMeasure T hT
g` is finite. -/
instance normalCFCDiagonalMeasure_finite (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    IsFiniteMeasure (normalCFCDiagonalMeasure T hT g) :=
  continuousRieszMeasure_finite (normalCFCDiagonalPositiveFunctional T hT g)

/-- **Regularity of a positive diagonal CFC measure.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. for `g ∈ H`, `ν_g=normalCFCDiagonalMeasure T hT g` is regular on the
compact spectrum `K`. -/
instance normalCFCDiagonalMeasure_regular (T : H →L[ℂ] H) (hT : IsStarNormal T) (g : H) :
    (normalCFCDiagonalMeasure T hT g).Regular :=
  continuousRieszMeasure_regular (normalCFCDiagonalPositiveFunctional T hT g)

/-- **Real integral representation of a diagonal CFC coefficient.** Let `H` be a complete
complex Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put
`K=σ_ℂ(T)` with its Borel measurable structure. for `g ∈ H`, `ν_g=normalCFCDiagonalMeasure
T hT g` and `f ∈ C(K,ℝ)`, `∫ f dν_g=normalCFCDiagonalRealFunctional T hT g f=Re
⟨g,f(T)g⟩`. -/
theorem normalCFCDiagonalMeasure_represents (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) (f : C(spectrum ℂ T, ℝ)) :
    ∫ x, f x ∂(normalCFCDiagonalMeasure T hT g) = normalCFCDiagonalRealFunctional T hT g f :=
  integral_continuousRieszMeasure (normalCFCDiagonalPositiveFunctional T hT g) f

/-- **Total diagonal spectral mass is the squared vector norm.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. for `g ∈ H`, `ν_g=normalCFCDiagonalMeasure T hT g` has
real mass `ν_g.real(K)=‖g‖²`. -/
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

/-- **Complexification of a positive diagonal measure.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g ∈ H`, the diagonal complex coefficient
`μ_(g,g)` is the complexification of `ν_g=normalCFCDiagonalMeasure T hT g`, with zero
imaginary measure. -/
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


/-- **Measurable diagonal coefficient equals positive mass.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g ∈ H` and measurable `s
⊆ K`, `μ_(g,g)(s)=(ν_g.real(s) : ℂ)`, where `ν_g=normalCFCDiagonalMeasure T hT g`. -/
theorem normalCFCCoefficientMeasure_diagonal_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    (normalCFCCoefficientMeasure T hT g g : ComplexMeasure (spectrum ℂ T)) s =
      ((normalCFCDiagonalMeasure T hT g).real s : ℂ) := by
  rw [normalCFCCoefficientMeasure_diagonal, SignedMeasure.toComplexMeasure_apply]
  simp only [Measure.toSignedMeasure_apply_measurable hs, _root_.zero_apply]
  apply Complex.ext <;>
    simp only [Complex.ofReal_re, Complex.ofReal_im]

/-- **Total complex diagonal mass.** Let `H` be a complete complex Hilbert space and `T : H
→L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel measurable
structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by `∫ f
dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g ∈ H`, `μ_(g,g)(K)=(‖g‖² : ℂ)`. -/
theorem normalCFCCoefficientMeasure_diagonal_univ (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g : H) :
    (normalCFCCoefficientMeasure T hT g g : ComplexMeasure (spectrum ℂ T)) univ =
      (‖g‖ ^ 2 : ℝ) := by
  rw [normalCFCCoefficientMeasure_diagonal_apply T hT g univ MeasurableSet.univ,
    normalCFCDiagonalMeasure_real_univ]

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

end
