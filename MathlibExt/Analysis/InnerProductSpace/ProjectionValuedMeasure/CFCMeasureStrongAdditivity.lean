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
# Strong countable additivity of the actual normal-CFC coefficient operators

The computed operators of disjoint measurable sets are orthogonal projections
by their actual intersection law. Their original complex coefficient measures
are countably additive. The existing strong orthogonal-projection sum is
therefore the computed operator of the union, identified on the same H by
its original inner coefficients. This supplies the strong-additivity field
needed by resolutionOfIdentity and borelFunctionalCalculus. No PVM, desired
limit, projection or coefficient-convergence certificate is an input.
Numbered textbook terminal theorem proofs remain wholly open.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Disjoint measurable computed coefficients sum in norm on every original vector. -/
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
