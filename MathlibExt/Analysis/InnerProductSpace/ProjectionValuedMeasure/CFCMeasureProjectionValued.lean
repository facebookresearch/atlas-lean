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

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureStrongAdditivity
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.Integral

/-!
# The PVM determined by a normal operator's continuous calculus

Let `T` be a normal bounded operator on a complete complex Hilbert space `H`. On the spectrum
`K=σ_ℂ(T)`, continuous functional calculus gives regular coefficient measures `μ_(g,h)` with `∫
f dμ_(g,h)=⟨h,f(T)g⟩` for continuous `f`.

The projections `E_T(s)` characterized by `⟨h,E_T(s)g⟩=μ_(g,h)(s)` form a strongly countably
additive PVM on `K`. Their scalar measures are regular. For `f ∈ C(K,ℂ)`, `∫ f dE_T=f(T)`, and
integrating the spectral coordinate `z ↦ z` gives `T`. The construction permits the zero Hilbert
space and an empty spectrum.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped CStarAlgebra InnerProductSpace
open MathlibExt.MeasureTheory
open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Spectral PVM from continuous functional calculus.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. `normalCFCPVM T hT` is the
strongly countably additive PVM `E_T` on `K`, determined by `⟨h,E_T(s)g⟩=μ_(g,h)(s)` for
measurable `s`, with zero on nonmeasurable sets. -/
def normalCFCPVM (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    ProjectionValuedMeasure (spectrum ℂ T) H where
  toFun := normalCFCCoefficientOperator T hT
  not_measurable' := fun hs => normalCFCCoefficientOperator_not_measurable T hT _ hs
  projection' := fun s _ => normalCFCCoefficientOperator_isStarProjection T hT s
  empty' := normalCFCCoefficientOperator_empty T hT
  univ' := normalCFCCoefficientOperator_univ T hT
  inter' := fun s hs t ht => (normalCFCCoefficientOperator_mul_inter T hT s hs t ht).symm
  m_iUnion' := normalCFCCoefficientOperator_m_iUnion T hT

/-- **Set projection of the CFC spectral measure.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for any set `s ⊆ K`, `(normalCFCPVM T
hT)(s)=normalCFCCoefficientOperator T hT s`, the operator determined on measurable `s` by
coefficient `μ_(g,h)(s)` and zero otherwise. -/
theorem normalCFCPVM_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) :
    normalCFCPVM T hT s = normalCFCCoefficientOperator T hT s := rfl

/-- **Scalar measure of the CFC spectral PVM.** Let `H` be a complete complex Hilbert space
and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `E_T=normalCFCPVM T hT` and `g,h ∈ H`, its
measure `s ↦ ⟨h,E_T(s)g⟩` equals the regular CFC coefficient measure
`normalCFCCoefficientMeasure T hT g h`. -/
theorem normalCFCPVM_scalarMeasure (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H) :
    (normalCFCPVM T hT).scalarMeasure g h =
      (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) := by
  apply VectorMeasure.ext
  intro s hs
  rw [scalarMeasure_apply, normalCFCPVM_apply]
  exact normalCFCCoefficientOperator_coefficient T hT s hs g h

/-- **Regular variation of CFC spectral coefficients.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. the total variation of each scalar measure `s ↦
⟨h,(normalCFCPVM T hT)(s)g⟩` is regular on the compact spectrum `K`. -/
theorem normalCFCPVM_scalarMeasure_regular (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) :
    _root_.MeasureTheory.VectorMeasure.HasRegularVariation ((normalCFCPVM T hT).scalarMeasure g h) := by
  rw [normalCFCPVM_scalarMeasure]
  exact (normalCFCCoefficientMeasure T hT g h).property

/-- **Continuous spectral integration equals CFC.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for every `f ∈ C(K,ℂ)`, `(normalCFCPVM T
hT).spectralIntegral f = cfcHom hT f = f(T)`, with `f` viewed as a bounded measurable
function. -/
theorem normalCFCPVM_spectralIntegral_continuous (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (f : C(spectrum ℂ T, ℂ)) :
    (normalCFCPVM T hT).spectralIntegral (BoundedMeasurableFunction.ofContinuousMap f) =
      cfcHom hT f := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  rw [inner_spectralIntegral_apply, normalCFCPVM_scalarMeasure, ← complexIntegralDual_apply]
  exact normalCFCCoefficientMeasure_represents T hT g h f

/-- **Recovery of a normal operator by its spectral coordinate.** Let `H` be a complete
complex Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put
`K=σ_ℂ(T)` with its Borel measurable structure. for `E_T=normalCFCPVM T hT`, `∫_K z
dE_T(z)=T`, integrating the continuous identity coordinate of the spectrum. -/
theorem normalCFCPVM_spectralIntegral_coordinate (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    (normalCFCPVM T hT).spectralIntegral
      (BoundedMeasurableFunction.ofContinuousMap
        ((ContinuousMap.id ℂ).restrict (spectrum ℂ T))) = T := by
  rw [normalCFCPVM_spectralIntegral_continuous]
  exact cfcHom_id hT

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

end
