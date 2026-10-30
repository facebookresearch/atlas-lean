/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Instances.Real
public import MathlibExt.Geometry.Manifold.Riemannian.Curvature

/-!
# Manifolds admitting a metric of positive scalar curvature

`Manifold.AdmitsPositiveScalarCurvatureMetric n M`: the smooth `n`-manifold `M` (modeled on `𝓡 n`,
so without boundary) carries a `C^∞` Riemannian metric whose scalar curvature is positive at every
point. Which manifolds have this property is the basic question of positive scalar curvature
geometry (M. Gromov, *101 Questions, Problems and Conjectures around Scalar Curvature* (2017),
[?1]: "What are possible topologies of manifolds which admit Riemannian metrics with scalar
curvatures `Sc > 0`?").

The metric ranges over all `C^∞` Riemannian metrics `g` on the tangent bundle
(`ContMDiffRiemannianMetric`). The scalar curvature is `Manifold.scalarCurvature` of `(M, g)`,
computed with `g` installed as the `RiemannianBundle` structure of the tangent bundle, so it does
not depend on any metric instance already present on `M`. No distance, completeness or
compactness is part of the property.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

namespace Manifold

/-- The smooth `n`-manifold `M` (modeled on `𝓡 n`) admits a metric of positive scalar curvature:
some `C^∞` Riemannian metric `g` on its tangent bundle has `scalarCurvature (𝓡 n) x > 0` at every
point `x`, the scalar curvature being computed for `g`. -/
def AdmitsPositiveScalarCurvatureMetric (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] : Prop :=
  ∃ g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x),
    letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x) := ⟨g.toRiemannianMetric⟩
    ∀ x : M, 0 < scalarCurvature (𝓡 n) x

end Manifold
