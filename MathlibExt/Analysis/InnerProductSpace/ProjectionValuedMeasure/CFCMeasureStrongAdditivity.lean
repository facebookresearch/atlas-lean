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

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.OrthogonalStrongSum
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureProjectionIntersection

/-!
# Strong countable additivity of normal CFC set operators

Let `T` be a normal operator on a complete complex Hilbert space and `P_s` its coefficient
operator for a subset of `σ_ℂ(T)`. For pairwise disjoint measurable sets `s_n`, the projections
`P_(s_n)` have orthogonal ranges.

Their strong sum satisfies `Σ_n P_(s_n)g=P_(⋃n s_n)g` in the Hilbert norm for every vector `g`.
Scalar coefficient measure additivity identifies this limit; operator-norm convergence is not
asserted.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Strong sum over disjoint measurable spectral sets.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable `s ⊆ K`, let
`P_s` be the bounded coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and set `P_s=0` for
nonmeasurable `s`. for pairwise disjoint measurable `s_n ⊆ K` and every `g ∈ H`, `HasSum
(fun n => P_(s_n)g) (P_(⋃n s_n)g)`, a norm-convergent vector series on the Hilbert space. -/
theorem normalCFCCoefficientOperator_m_iUnion
    (T : H →L[ℂ] H) (hT : IsStarNormal T) (s : ℕ → Set (spectrum ℂ T))
    (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise fun i j => Disjoint (s i) (s j)) (g : H) :
    HasSum (fun n => normalCFCCoefficientOperator T hT (s n) g)
      (normalCFCCoefficientOperator T hT (⋃ n, s n) g) := by
  have hprojection (n : ℕ) : IsStarProjection (normalCFCCoefficientOperator T hT (s n)) :=
    normalCFCCoefficientOperator_isStarProjection T hT (s n)
  have horth : Pairwise fun i j =>
      normalCFCCoefficientOperator T hT (s i) * normalCFCCoefficientOperator T hT (s j) = 0 := by
    intro i j hij
    rw [normalCFCCoefficientOperator_mul_inter T hT (s i) (hs i) (s j) (hs j),
      Set.disjoint_iff_inter_eq_empty.mp (hdisj hij), normalCFCCoefficientOperator_empty]
  refine (hasSum_of_orthogonal_of_inner_hasSum
    (fun n => normalCFCCoefficientOperator T hT (s n)) hprojection horth
    (normalCFCCoefficientOperator T hT (⋃ n, s n)) ?_) g
  intro x h
  have hu : MeasurableSet (⋃ n, s n) := MeasurableSet.iUnion hs
  have hf : (fun n => ⟪h, normalCFCCoefficientOperator T hT (s n) x⟫_ℂ) =
      (fun n => (normalCFCCoefficientMeasure T hT x h : ComplexMeasure (spectrum ℂ T)) (s n)) := by
    funext n
    exact normalCFCCoefficientOperator_coefficient T hT (s n) (hs n) x h
  rw [hf, normalCFCCoefficientOperator_coefficient T hT (⋃ n, s n) hu x h]
  exact VectorMeasure.m_iUnion
    (normalCFCCoefficientMeasure T hT x h : ComplexMeasure (spectrum ℂ T)) hs hdisj

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
