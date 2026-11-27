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

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureCoefficientBounds
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Bounded set operators from normal CFC coefficient measures

For a normal bounded operator `T` on a complete complex Hilbert space, let `μ_(g,h)` be its
regular continuous-functional-calculus coefficient measure on `K=σ_ℂ(T)`. On a measurable set `s
⊆ K`, the form `F_s(h,g)=μ_(g,h)(s)` is bounded sesquilinear with norm at most one.

The Hilbert representation of this form gives the bounded operator `P_s` with `⟨h,P_s
g⟩=μ_(g,h)(s)` and `‖P_s‖≤1`. Set `P_s=0` for nonmeasurable `s`. These coefficient operators are
defined without a supplied PVM; their projection and countable-additivity properties are proved
separately.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Bounded sesquilinear form of a CFC set coefficient.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for measurable `s ⊆ K`,
`normalCFCCoefficientBilin T hT s hs (h,g)=μ_(g,h)(s)`, conjugate-linear in `h` and linear
in `g`, with bound `|F_s(h,g)|≤‖h‖‖g‖`. -/
def normalCFCCoefficientBilin (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  (normalCFCCoefficientFormLinear T hT s).mkContinuous₂ 1 (normalCFCCoefficientFormLinear_norm_apply_le T hT s hs)

/-- **Value of a continuous CFC coefficient form.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for measurable `s ⊆ K` and `g,h ∈ H`,
`normalCFCCoefficientBilin T hT s hs h g=μ_(g,h)(s)`. -/
theorem normalCFCCoefficientBilin_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) (h g : H) :
    normalCFCCoefficientBilin T hT s hs h g =
      (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s := by
  rw [normalCFCCoefficientBilin, LinearMap.mkContinuous₂_apply,
    normalCFCCoefficientFormLinear_apply]

/-- **Norm bound for a CFC set coefficient form.** Let `H` be a complete complex Hilbert space
and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for measurable `s ⊆ K`, the bounded
sesquilinear form `F_s(h,g)=μ_(g,h)(s)` has bilinear operator norm at most one. -/
theorem normalCFCCoefficientBilin_norm_le (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    ‖normalCFCCoefficientBilin T hT s hs‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le (normalCFCCoefficientFormLinear T hT s) zero_le_one
    (normalCFCCoefficientFormLinear_norm_apply_le T hT s hs)

private theorem rieszCoefficientOperator_norm_le (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    ‖_root_.InnerProductSpace.continuousLinearMapOfBilin (normalCFCCoefficientBilin T hT s hs)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  change ‖(_root_.InnerProductSpace.toDual ℂ H).symm
    (normalCFCCoefficientBilin T hT s hs h)‖ ≤ 1 * ‖h‖
  rw [(_root_.InnerProductSpace.toDual ℂ H).symm.norm_map]
  exact ((normalCFCCoefficientBilin T hT s hs).le_opNorm h).trans
    (mul_le_mul_of_nonneg_right (normalCFCCoefficientBilin_norm_le T hT s hs) (norm_nonneg h))

/-- **Bounded operator representing a CFC set coefficient.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for measurable `s ⊆ K`,
`normalCFCCoefficientOperator T hT s=P_s` is characterized by `⟨h,P_s g⟩=μ_(g,h)(s)` for
all `g,h`. Nonmeasurable sets have operator zero. -/
def normalCFCCoefficientOperator (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) : H →L[ℂ] H := by
  classical
  exact if hs : MeasurableSet s then
    (_root_.InnerProductSpace.continuousLinearMapOfBilin
      (normalCFCCoefficientBilin T hT s hs)).adjoint
  else 0

/-- **Hilbert representation of a measurable CFC coefficient.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for measurable `s ⊆ K`, let
`A_s` be the bounded operator with `⟨A_s h,g⟩=μ_(g,h)(s)`. Then
`normalCFCCoefficientOperator T hT s=A_s*`; equivalently its coefficient is `⟨h,P_s
g⟩=μ_(g,h)(s)`. -/
theorem normalCFCCoefficientOperator_of_measurable (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    normalCFCCoefficientOperator T hT s =
      (_root_.InnerProductSpace.continuousLinearMapOfBilin
        (normalCFCCoefficientBilin T hT s hs)).adjoint := by
  rw [normalCFCCoefficientOperator, dite_eq_left hs]

/-- **Zero CFC coefficient operator on a nonmeasurable set.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. if `s ⊆ K` is not measurable,
`normalCFCCoefficientOperator T hT s=0`. -/
theorem normalCFCCoefficientOperator_not_measurable (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : ¬ MeasurableSet s) :
    normalCFCCoefficientOperator T hT s = 0 := by
  rw [normalCFCCoefficientOperator, dite_eq_right hs]

/-- **Matrix coefficient of a CFC set operator.** Let `H` be a complete complex Hilbert space
and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for measurable `s ⊆ K` and `g,h ∈ H`,
`⟨h,normalCFCCoefficientOperator T hT s g⟩=μ_(g,h)(s)`. -/
theorem normalCFCCoefficientOperator_coefficient (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) (g h : H) :
    ⟪h, normalCFCCoefficientOperator T hT s g⟫_ℂ =
      (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s := by
  rw [normalCFCCoefficientOperator_of_measurable T hT s hs,
    ContinuousLinearMap.adjoint_inner_right,
    _root_.InnerProductSpace.continuousLinearMapOfBilin_apply,
    normalCFCCoefficientBilin_apply]

/-- **Contraction bound for every CFC set operator.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for every set `s ⊆ K`,
`‖normalCFCCoefficientOperator T hT s‖≤1`, including nonmeasurable sets and the zero
Hilbert space. -/
theorem normalCFCCoefficientOperator_norm_le (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) : ‖normalCFCCoefficientOperator T hT s‖ ≤ 1 := by
  classical
  by_cases hs : MeasurableSet s
  · rw [normalCFCCoefficientOperator_of_measurable T hT s hs, LinearIsometryEquiv.norm_map]
    exact rieszCoefficientOperator_norm_le T hT s hs
  · rw [normalCFCCoefficientOperator_not_measurable T hT s hs, norm_zero]
    exact zero_le_one

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

end
