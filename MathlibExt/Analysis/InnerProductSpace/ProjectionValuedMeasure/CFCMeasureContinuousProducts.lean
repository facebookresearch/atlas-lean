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
# Continuous calculus factors in spectral coefficient measures

For a normal operator `T` on a complete complex Hilbert space, its coefficient measures satisfy
`∫ q dμ_(f(T)g,h)=∫ q f dμ_(g,h)` and `∫ q dμ_(g,f(T)h)=∫ q conj(f) dμ_(g,h)` for continuous
`f,q` on `K=σ_ℂ(T)`.

In particular, `μ_(f(T)g,h)=μ_(g,conj(f)(T)h)` as regular complex measures. These identities
follow the inner-product convention linear in the second argument.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped CStarAlgebra InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Continuous factor from the first CFC coefficient vector.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g,h ∈ H` and `f,q ∈
C(K,ℂ)`, `∫ q dμ_(f(T)g,h)=∫ q*f dμ_(g,h)`. -/
theorem normalCFCCoefficientMeasure_cfc_mul_left (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (f q : C(spectrum ℂ T, ℂ)) :
    MathlibExt.MeasureTheory.complexIntegralDual
      (normalCFCCoefficientMeasure T hT (cfcHom hT f g) h) q =
    MathlibExt.MeasureTheory.complexIntegralDual (normalCFCCoefficientMeasure T hT g h) (q * f) := by
  rw [normalCFCCoefficientMeasure_represents, normalCFCCoefficientMeasure_represents, map_mul]
  rfl

/-- **Adjoint continuous factor in the second coefficient vector.** Let `H` be a complete
complex Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put
`K=σ_ℂ(T)` with its Borel measurable structure. Let `μ_(g,h)` be the regular complex
measure on `K` characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g,h ∈ H`
and `f,q ∈ C(K,ℂ)`, `∫ q dμ_(g,conj(f)(T)h)=∫ q*f dμ_(g,h)`. -/
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

/-- **Conjugated integrand from the second coefficient vector.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g,h ∈ H` and `f,q ∈
C(K,ℂ)`, `∫ q dμ_(g,f(T)h)=∫ q*conj(f) dμ_(g,h)`. -/
theorem normalCFCCoefficientMeasure_cfc_mul_right (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (f q : C(spectrum ℂ T, ℂ)) :
    MathlibExt.MeasureTheory.complexIntegralDual
      (normalCFCCoefficientMeasure T hT g (cfcHom hT f h)) q =
    MathlibExt.MeasureTheory.complexIntegralDual (normalCFCCoefficientMeasure T hT g h) (q * star f) := by
  simpa only [star_star] using
    normalCFCCoefficientMeasure_cfc_star_mul_right T hT g h (star f) q

/-- **Balancing a continuous CFC factor across coefficient vectors.** Let `H` be a complete
complex Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put
`K=σ_ℂ(T)` with its Borel measurable structure. Let `μ_(g,h)` be the regular complex
measure on `K` characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g,h ∈ H`
and `f ∈ C(K,ℂ)`, `μ_(f(T)g,h)=μ_(g,conj(f)(T)h)` as regular complex measures. -/
theorem normalCFCCoefficientMeasure_cfc_balance (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (f : C(spectrum ℂ T, ℂ)) :
    normalCFCCoefficientMeasure T hT (cfcHom hT f g) h =
    normalCFCCoefficientMeasure T hT g (cfcHom hT (star f) h) := by
  apply MathlibExt.MeasureTheory.complexIntegralDual_injective
  ext q
  rw [normalCFCCoefficientMeasure_cfc_mul_left, normalCFCCoefficientMeasure_cfc_star_mul_right]

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
