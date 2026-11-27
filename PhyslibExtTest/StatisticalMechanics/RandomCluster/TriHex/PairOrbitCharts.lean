/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PairOrbitCharts

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PairOrbitCharts`

* `siteLexNonnegative` holds for `(0, 3)` and fails for `(-1, 5)`;
* `triangularPairNormal 0 (-1, 0)` is based at `(-1, 0)` (the displacement is flipped);
* `triHexFullDualEdgeEquiv_indexedEdge` sends `s(0, (1, 0))` to `s((0, false), ((1, 0), true))`;
* `triangularNonedgePairShape_not_edge` and `triHexFullDualEdgeEquiv_mem_edgeSet`: the non-edge
  `s(0, (2, 0))` is sent to a non-edge.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PairOrbitCharts

open _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

-- Lexicographic nonnegativity on concrete displacements.
example : siteLexNonnegative ![0, 3] := by
  simp [siteLexNonnegative]

example : ¬ siteLexNonnegative ![-1, 5] := by
  simp [siteLexNonnegative]

-- The normal form of a pair with negative displacement is based at the other endpoint.
example : (triangularPairNormal 0 ![-1, 0]).1 = ![-1, 0] := by
  simp [triangularPairNormal, siteLexNonnegative]

-- The extended duality on the horizontal edge at the origin.
example : triHexFullDualEdgeEquiv s(0, 0 + triangularStep 0) =
    s(((0 : Site 2), false), (0 + hexagonalStep 0, true)) := by
  rw [show s((0 : Site 2), 0 + triangularStep 0) = triangularIndexedEdge (0, 0) from rfl,
    triHexFullDualEdgeEquiv_indexedEdge]
  simp [triHexIndexEquiv, hexagonalIndexedEdge]

-- The long shape is not an edge shape.
example : ¬ IsTriangularEdgePairShape (triangularNonedgePairShape 0) :=
  triangularNonedgePairShape_not_edge 0

-- A non-edge goes to a non-edge.
example : triHexFullDualEdgeEquiv s(0, ![2, 0]) ∉ hexagonalGraph.edgeSet := by
  rw [← triHexFullDualEdgeEquiv_mem_edgeSet]
  simp [triangularAdj, Fin.exists_fin_succ, triangularStep, funext_iff, Fin.forall_fin_two]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PairOrbitCharts
