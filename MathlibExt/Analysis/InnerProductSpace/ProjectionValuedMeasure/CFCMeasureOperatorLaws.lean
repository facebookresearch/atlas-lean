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

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureOperators
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureCoefficientBounds

/-!
# Self-adjointness and normalization of CFC set operators

For a normal operator `T` on a complete complex Hilbert space, its CFC coefficient measure on
`K=σ_ℂ(T)` has total value `μ_(g,h)(K)=⟨h,g⟩`.

The set operators `P_s` with coefficients `⟨h,P_s g⟩=μ_(g,h)(s)` are self-adjoint. They satisfy
`P_∅=0` and `P_K=I_H`; nonmeasurable sets have value zero. No projection-valued measure is a
premise of these normalization laws.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
open MathlibExt.MeasureTheory
open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Total mass of a normal CFC coefficient measure.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g,h ∈ H`, `μ_(g,h)(K)=⟨h,g⟩`. -/
theorem normalCFCCoefficientMeasure_univ (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H) :
    (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) univ = ⟪h, g⟫_ℂ := by
  let mu := normalCFCCoefficientMeasure T hT g h
  have h1 : BoundedMeasurableFunction.ofContinuousMap (1 : C(spectrum ℂ T, ℂ)) =
      BoundedMeasurableFunction.indicatorConst univ MeasurableSet.univ 1 := by
    apply Subtype.ext
    apply lp.ext
    funext x
    simp [BoundedMeasurableFunction.ofContinuousMap_apply,
      BoundedMeasurableFunction.indicatorConst_apply]
  have hi : complexIntegralDual mu (1 : C(spectrum ℂ T, ℂ)) =
      (mu : ComplexMeasure (spectrum ℂ T)) univ := by
    rw [complexIntegralDual_apply, h1, complexIntegral_indicatorConst, one_mul]
  have hr := normalCFCCoefficientMeasure_represents T hT g h (1 : C(spectrum ℂ T, ℂ))
  change complexIntegralDual mu 1 = _ at hr
  rw [hi, map_one] at hr
  simpa only [one_apply_eq_self] using hr

/-- **Self-adjointness of every CFC set operator.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable `s ⊆ K`, let `P_s` be the
bounded coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and set `P_s=0` for
nonmeasurable `s`. for every set `s ⊆ K`, `P_s*=P_s`, including the zero value for
nonmeasurable `s`. -/
theorem normalCFCCoefficientOperator_isSelfAdjoint (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) : IsSelfAdjoint (normalCFCCoefficientOperator T hT s) := by
  classical
  by_cases hs : MeasurableSet s
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    calc
      ⟪normalCFCCoefficientOperator T hT s x, y⟫_ℂ =
          star ⟪y, normalCFCCoefficientOperator T hT s x⟫_ℂ :=
        (inner_conj_symm (𝕜 := ℂ) (normalCFCCoefficientOperator T hT s x) y).symm
      _ = star ((normalCFCCoefficientMeasure T hT x y : ComplexMeasure (spectrum ℂ T)) s) := by
        rw [normalCFCCoefficientOperator_coefficient T hT s hs x y]
      _ = (normalCFCCoefficientMeasure T hT y x : ComplexMeasure (spectrum ℂ T)) s :=
        (normalCFCCoefficientMeasure_conj_symm T hT y x s hs).symm
      _ = ⟪x, normalCFCCoefficientOperator T hT s y⟫_ℂ :=
        (normalCFCCoefficientOperator_coefficient T hT s hs y x).symm
  · rw [normalCFCCoefficientOperator_not_measurable T hT s hs]
    exact IsSelfAdjoint.zero (H →L[ℂ] H)

/-- **Empty CFC set operator is zero.** Let `H` be a complete complex Hilbert space and `T : H
→L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel measurable
structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by `∫ f
dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable `s ⊆ K`, let `P_s` be the bounded
coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and set `P_s=0` for nonmeasurable `s`.
`P_∅=normalCFCCoefficientOperator T hT ∅=0`. -/
theorem normalCFCCoefficientOperator_empty (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    normalCFCCoefficientOperator T hT ∅ = 0 := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  rw [normalCFCCoefficientOperator_coefficient T hT ∅ MeasurableSet.empty g h,
    VectorMeasure.empty]
  simp

/-- **Full-spectrum CFC set operator is the identity.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable `s ⊆ K`, let `P_s` be the
bounded coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and set `P_s=0` for
nonmeasurable `s`. `P_K=normalCFCCoefficientOperator T hT K=I_H`, including the zero
Hilbert space. -/
theorem normalCFCCoefficientOperator_univ (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    normalCFCCoefficientOperator T hT univ = 1 := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  rw [normalCFCCoefficientOperator_coefficient T hT univ MeasurableSet.univ g h,
    normalCFCCoefficientMeasure_univ]
  rfl

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

end
