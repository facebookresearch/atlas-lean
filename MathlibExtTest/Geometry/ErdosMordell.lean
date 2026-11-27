/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Geometry.ErdosMordell
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Geometry.Euclidean.Projection

open Affine EuclideanGeometry
open scoped EuclideanGeometry

namespace MathlibExt.Geometry.ErdosProblem898Wanted

-- Apply the inequality at the centroid, measuring distances directly to the side lines.
example (b : AffineBasis (Fin 3) ℝ ℝ²) :
    let P := Finset.univ.centroid ℝ b
    2 * (Metric.infDist P line[ℝ, b 1, b 2] + Metric.infDist P line[ℝ, b 0, b 1] +
      Metric.infDist P line[ℝ, b 2, b 0]) ≤ dist P (b 0) + dist P (b 1) + dist P (b 2) := by
  intro P
  have hfeet (A B : ℝ²) :
      line[ℝ, P, (orthogonalProjection line[ℝ, A, B] P : ℝ²)].direction ⟂
        line[ℝ, A, B].direction := by
    rw [Submodule.isOrtho_iff_le, direction_affineSpan, vectorSpan_pair,
      Submodule.span_singleton_le_iff_mem]
    exact vsub_orthogonalProjection_mem_direction_orthogonal _ _
  have hb : (b : Fin 3 → ℝ²) = ![b 0, b 1, b 2] := by funext i; fin_cases i <;> rfl
  have hi := b.ind
  have hp : P ∈ interior (convexHull ℝ (Set.range b)) := b.centroid_mem_interior_convexHull
  rw [hb] at hi hp
  rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union] at hp
  rw [← dist_orthogonalProjection_eq_infDist, ← dist_orthogonalProjection_eq_infDist,
    ← dist_orthogonalProjection_eq_infDist]
  exact conjecture_holds _ _ _ P _ _ _ hi hp (orthogonalProjection_mem _) (hfeet _ _)
    (orthogonalProjection_mem _) (hfeet _ _) (orthogonalProjection_mem _) (hfeet _ _)

end MathlibExt.Geometry.ErdosProblem898Wanted
