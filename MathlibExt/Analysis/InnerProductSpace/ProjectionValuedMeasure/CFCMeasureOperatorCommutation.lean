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
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureContinuousProducts

/-!
# Spectral coefficient operators commute with continuous calculus

For a normal operator `T` on a complete complex Hilbert space, let `P_s` be the set operator
with `⟨h,P_s g⟩=μ_(g,h)(s)` on measurable subsets of `σ_ℂ(T)`, and zero on nonmeasurable
subsets.

For every continuous function `f` on the spectrum, `P_s f(T)=f(T)P_s`. This applies to every set
`s`, including the zero value for nonmeasurable sets, and permits a zero Hilbert space.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
open scoped CStarAlgebra InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Commutation of a spectral set operator with continuous CFC.** Let `H` be a complete
complex Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put
`K=σ_ℂ(T)` with its Borel measurable structure. Let `μ_(g,h)` be the regular complex
measure on `K` characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable
`s ⊆ K`, let `P_s` be the bounded coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and
set `P_s=0` for nonmeasurable `s`. for every set `s ⊆ K` and `f ∈ C(K,ℂ)`, `P_s
f(T)=f(T)P_s`, equivalently `Commute (normalCFCCoefficientOperator T hT s) (cfcHom hT f)`. -/
theorem normalCFCCoefficientOperator_commute_cfc (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (f : C(spectrum ℂ T, ℂ)) :
    Commute (normalCFCCoefficientOperator T hT s) (cfcHom hT f) := by
  classical
  change normalCFCCoefficientOperator T hT s * cfcHom hT f =
    cfcHom hT f * normalCFCCoefficientOperator T hT s
  by_cases hs : MeasurableSet s
  · apply ContinuousLinearMap.ext
    intro g
    apply ext_inner_left ℂ
    intro h
    change ⟪h, normalCFCCoefficientOperator T hT s (cfcHom hT f g)⟫_ℂ =
      ⟪h, cfcHom hT f (normalCFCCoefficientOperator T hT s g)⟫_ℂ
    calc
      ⟪h, normalCFCCoefficientOperator T hT s (cfcHom hT f g)⟫_ℂ =
          (normalCFCCoefficientMeasure T hT (cfcHom hT f g) h :
            ComplexMeasure (spectrum ℂ T)) s :=
        normalCFCCoefficientOperator_coefficient T hT s hs (cfcHom hT f g) h
      _ = (normalCFCCoefficientMeasure T hT g (cfcHom hT (star f) h) :
            ComplexMeasure (spectrum ℂ T)) s :=
        congrArg (fun mu : MathlibExt.MeasureTheory.RegularComplexMeasure (spectrum ℂ T) =>
          (mu : ComplexMeasure (spectrum ℂ T)) s)
          (normalCFCCoefficientMeasure_cfc_balance T hT g h f)
      _ = ⟪cfcHom hT (star f) h, normalCFCCoefficientOperator T hT s g⟫_ℂ :=
        (normalCFCCoefficientOperator_coefficient T hT s hs g (cfcHom hT (star f) h)).symm
      _ = ⟪h, cfcHom hT f (normalCFCCoefficientOperator T hT s g)⟫_ℂ := by
        rw [map_star]
        change ⟪(cfcHom hT f).adjoint h, normalCFCCoefficientOperator T hT s g⟫_ℂ =
          ⟪h, cfcHom hT f (normalCFCCoefficientOperator T hT s g)⟫_ℂ
        exact ContinuousLinearMap.adjoint_inner_left (cfcHom hT f)
          (normalCFCCoefficientOperator T hT s g) h
  · rw [normalCFCCoefficientOperator_not_measurable T hT s hs, zero_mul, mul_zero]

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
