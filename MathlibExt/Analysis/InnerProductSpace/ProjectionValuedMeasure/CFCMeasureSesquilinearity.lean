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
# Sesquilinearity of normal CFC coefficient measures

For a normal bounded operator `T` on a complete complex Hilbert space, write `μ_(g,h)` for the
regular complex measure on `σ_ℂ(T)` with `∫ f dμ_(g,h)=⟨h,f(T)g⟩` on continuous functions.

The measure is additive and complex-linear in `g`, and additive and conjugate-linear in `h`. In
particular, a zero coefficient vector gives the zero measure. The convention is the complex
inner product linear in its second argument.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped CStarAlgebra InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Addition in the first CFC coefficient vector.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g₁,g₂,h ∈ H`,
`μ_(g₁+g₂,h)=μ_(g₁,h)+μ_(g₂,h)` as regular complex measures. -/
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

/-- **Complex linearity in the first coefficient vector.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `c : ℂ` and `g,h ∈ H`,
`μ_(c • g,h)=c • μ_(g,h)`. -/
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

/-- **Addition in the second CFC coefficient vector.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g,h₁,h₂ ∈ H`,
`μ_(g,h₁+h₂)=μ_(g,h₁)+μ_(g,h₂)`. -/
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

/-- **Conjugate linearity in the second coefficient vector.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `c : ℂ` and `g,h ∈ H`,
`μ_(g,c • h)=conj(c) • μ_(g,h)`. -/
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

/-- **Zero first vector of a CFC coefficient measure.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `h ∈ H`, `μ_(0,h)=0`. -/
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

/-- **Zero second vector of a CFC coefficient measure.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g ∈ H`, `μ_(g,0)=0`. -/
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
