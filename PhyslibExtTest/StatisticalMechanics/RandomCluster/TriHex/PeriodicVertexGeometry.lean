/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicVertexGeometry

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicVertexGeometry`

* `triHexPlanePeriod ![2, 3] = 2 + 3 I`;
* the black hexagonal vertex `(0, false)` sits at the face centre `1 / 3 + I / 3`;
* `triangularStraightEdge_length_le_two` on the concrete edge `s(0, (1, 0))`;
* `triangularStraightEdgeArc_locallyFinite` on the closed unit disc.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicVertexGeometry

open _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

-- The period map on a concrete site.
example : triHexPlanePeriod ![2, 3] = 2 + 3 * Complex.I := by
  apply Complex.ext <;> simp

-- The black hexagonal vertex at the origin sits at the centre of the upward face.
example : (hexagonalPlaneVertex ((0 : Site 2), false) : ℂ) =
    (1 / 3 : ℝ) + (1 / 3 : ℝ) * Complex.I := by
  simp [hexagonalPlaneVertexValue]

/-- The horizontal edge at the origin is a triangular edge. -/
theorem adj_zero : triangularGraph.Adj 0 (0 + triangularStep 0) :=
  (SimpleGraph.mem_edgeSet _).1 (triangularIndexedEdge_mem (0, 0))

-- The horizontal edge at the origin has length at most `2`.
example : dist (triangularPlaneVertex 0) (triangularPlaneVertex (0 + triangularStep 0)) ≤ 2 :=
  triangularStraightEdge_length_le_two adj_zero

-- Only finitely many straight edges meet the closed unit disc.
example : {xy : Site 2 × Site 2 | ∃ hxy : triangularGraph.Adj xy.1 xy.2,
    (Set.range (triangularStraightEdgeArc hxy) ∩ Metric.closedBall 0 1).Nonempty}.Finite :=
  triangularStraightEdgeArc_locallyFinite _ (isCompact_closedBall 0 1)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicVertexGeometry
