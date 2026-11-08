/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.PositiveScalarCurvature

/-!
# Tests for `Manifold.AdmitsPositiveScalarCurvatureMetric`

The predicate unfolds to the existence of a `C^∞` metric with positive scalar curvature everywhere,
it elaborates on a positive-dimensional model, and it fails on the nonempty `0`-manifold `ℝ⁰`, where
the scalar curvature of every metric is a trace over the zero space, hence `0`.
-/

open Bundle Manifold
open scoped Manifold ContDiff

namespace PositiveScalarCurvatureTests

/-- The predicate is the existence of a `C^∞` metric whose scalar curvature is positive at every
point. -/
example (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] :
    AdmitsPositiveScalarCurvatureMetric n M ↔
      ∃ g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
          (fun x : M ↦ TangentSpace (𝓡 n) x),
        letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x) := ⟨g.toRiemannianMetric⟩
        ∀ x : M, 0 < scalarCurvature (𝓡 n) x :=
  Iff.rfl

/-- The predicate elaborates on a positive-dimensional manifold. -/
example : Prop := AdmitsPositiveScalarCurvatureMetric 3 (EuclideanSpace ℝ (Fin 3))

/-- The nonempty `0`-manifold `ℝ⁰` admits no metric of positive scalar curvature: for every metric,
the scalar curvature at the origin is a sum over an orthonormal basis of the zero tangent space,
which is empty. -/
example : ¬ AdmitsPositiveScalarCurvatureMetric 0 (EuclideanSpace ℝ (Fin 0)) := by
  rintro ⟨g, hg⟩
  let _ : RiemannianBundle (fun x : EuclideanSpace ℝ (Fin 0) ↦ TangentSpace (𝓡 0) x) :=
    ⟨g.toRiemannianMetric⟩
  have hpos := hg 0
  have hzero : scalarCurvature (𝓡 0) (0 : EuclideanSpace ℝ (Fin 0)) = 0 := by
    unfold scalarCurvature
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hrank : Module.finrank ℝ (TangentSpace (𝓡 0) (0 : EuclideanSpace ℝ (Fin 0))) = 0 :=
      finrank_euclideanSpace_fin
    exact (Fin.cast hrank i).elim0
  exact lt_irrefl _ (hzero ▸ hpos)

end PositiveScalarCurvatureTests
