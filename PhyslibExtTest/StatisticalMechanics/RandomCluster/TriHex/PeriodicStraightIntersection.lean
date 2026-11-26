/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicStraightIntersection

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicStraightIntersection`

* `triangularStraightEdgeIntersection` and `hexagonalStraightEdgeIntersection` discharge the
  hypotheses of the conditional embeddings, which they unfold to;
* `triangularPeriodicPlaneEmbedding.edgeArc_disjoint` separates the parallel edges
  `s(0, (1, 0))` and `s((0, 2), (0, 2) + (1, 0))`;
* `triangularCanonicalSegments_commonEndpoint`: the origin lies on the edges in directions `0`
  and `1` from the origin, so they share an endpoint;
* `hexagonalScaledCoordinate` on the white vertex at the origin.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicStraightIntersection

open _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

-- The unconditional embeddings are the conditional ones applied to the proved properties.
example : triangularPeriodicPlaneEmbedding =
    triangularPeriodicPlaneEmbedding_of_intersection triangularStraightEdgeIntersection :=
  rfl

example : hexagonalPeriodicPlaneEmbedding =
    hexagonalPeriodicPlaneEmbedding_of_intersection hexagonalStraightEdgeIntersection :=
  rfl

-- Two vertex-disjoint parallel edges have disjoint segments in the embedding.
example :
    Disjoint
      (Set.range (triangularPeriodicPlaneEmbedding.edgeArc
        ((SimpleGraph.mem_edgeSet _).1 (triangularIndexedEdge_mem (0, 0)))))
      (Set.range (triangularPeriodicPlaneEmbedding.edgeArc
        ((SimpleGraph.mem_edgeSet _).1 (triangularIndexedEdge_mem (![0, 2], 0))))) := by
  apply triangularPeriodicPlaneEmbedding.edgeArc_disjoint <;>
    simp [triangularStep, funext_iff, Fin.forall_fin_two]

-- Two segments through the origin share an endpoint.
example : (0 : Site 2) = 0 ∨ (0 : Site 2) = 0 + triangularStep 1 ∨
    0 + triangularStep 0 = 0 ∨ 0 + triangularStep 0 = 0 + triangularStep 1 :=
  triangularCanonicalSegments_commonEndpoint 0 0 0 1 (triangularPlaneVertex 0)
    ⟨0, Path.source _⟩ ⟨0, Path.source _⟩

-- Scaled coordinates of the white vertex at the origin.
example : (hexagonalPlaneVertex ((0 : Site 2), true) : ℂ).re = -1 / 3 := by
  rw [hexagonalPlaneVertex_re_scaled]
  simp [hexagonalScaledCoordinate]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicStraightIntersection
