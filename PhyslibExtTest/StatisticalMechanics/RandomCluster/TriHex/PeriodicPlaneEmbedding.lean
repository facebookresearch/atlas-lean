/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicPlaneEmbedding

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicPlaneEmbedding`

All checks are conditional on `TriangularStraightEdgeIntersectionProperty` (proved downstream in
`TriHex.PeriodicStraightIntersection`):
* `triangularPeriodicPlaneEmbedding_of_intersection` has vertex map `triangularPlaneVertex` and
  sends the period `(1, 0)` to `1`;
* `triangularStraightEdgeArc_disjoint_of_intersection` separates the parallel edges
  `s(0, (1, 0))` and `s((0, 2), (0, 2) + (1, 0))`;
* the hexagonal embedding places `(0, true)` at `-1 / 3 - I / 3`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicPlaneEmbedding

open _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

-- The packaged embedding uses the straight-drawing vertex map and period.
example (h : TriangularStraightEdgeIntersectionProperty) :
    (triangularPeriodicPlaneEmbedding_of_intersection h).vertex = triangularPlaneVertex :=
  rfl

example (h : TriangularStraightEdgeIntersectionProperty) :
    (triangularPeriodicPlaneEmbedding_of_intersection h).period ![1, 0] = 1 := by
  apply Complex.ext <;> simp [triangularPeriodicPlaneEmbedding_of_intersection]

-- Two vertex-disjoint parallel edges have disjoint segments.
example (h : TriangularStraightEdgeIntersectionProperty) :
    Disjoint
      (Set.range (triangularStraightEdgeArc
        ((SimpleGraph.mem_edgeSet _).1 (triangularIndexedEdge_mem (0, 0)))))
      (Set.range (triangularStraightEdgeArc
        ((SimpleGraph.mem_edgeSet _).1 (triangularIndexedEdge_mem (![0, 2], 0))))) := by
  apply triangularStraightEdgeArc_disjoint_of_intersection h <;>
    simp [triangularStep, funext_iff, Fin.forall_fin_two]

-- The hexagonal embedding places the white vertex at the origin.
example (h : HexagonalStraightEdgeIntersectionProperty) :
    ((hexagonalPeriodicPlaneEmbedding_of_intersection h).vertex ((0 : Site 2), true) : ℂ) =
      -(1 / 3 : ℝ) - (1 / 3 : ℝ) * Complex.I := by
  simp [hexagonalPeriodicPlaneEmbedding_of_intersection, hexagonalPlaneVertexValue]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicPlaneEmbedding
