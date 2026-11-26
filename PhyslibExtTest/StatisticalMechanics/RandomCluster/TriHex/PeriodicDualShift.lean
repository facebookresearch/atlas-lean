/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicDualShift

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicDualShift`

* `triangularEdgeTranslate_val`: translating the edge `s(0, (1, 0))` by `(0, 1)` gives
  `s((0, 1), (1, 0) + (0, 1))`;
* `triangularIndexedEdge_add` on a concrete index and shift;
* `triHexDualEdgeEquiv_add`: duality commutes with translation of a concrete edge;
* translating by `0` fixes every hexagonal edge (via `hexagonalEdgeTranslate_val`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicDualShift

open _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

-- Translating a concrete triangular edge.
example : ((triangularEdgeTranslate ![0, 1] (triangularEdgeChart (0, 0)) :
      triangularGraph.edgeSet) : Sym2 (Site 2)) =
    s(![0, 1], triangularStep 0 + ![0, 1]) := by
  rw [triangularEdgeTranslate_val]
  simp [triangularEdgeChart, triangularIndexedEdge]

-- Index translation on a concrete edge.
example : triangularIndexedEdge ((0 : Site 2) + ![2, 3], 1) =
    Sym2.map (siteTranslate ![2, 3]) (triangularIndexedEdge (0, 1)) :=
  triangularIndexedEdge_add ![2, 3] (0, 1)

-- Duality commutes with translation of the horizontal edge at the origin.
example : triHexDualEdgeEquiv (triangularEdgeTranslate ![1, -1] (triangularEdgeChart (0, 0))) =
    hexagonalEdgeTranslate ![1, -1] (triHexDualEdgeEquiv (triangularEdgeChart (0, 0))) :=
  triHexDualEdgeEquiv_add _ _

-- Translation by zero is the identity on hexagonal edges.
example (e : hexagonalGraph.edgeSet) : hexagonalEdgeTranslate 0 e = e := by
  apply Subtype.ext
  rw [hexagonalEdgeTranslate_val]
  induction (e : Sym2 HexVertex) using Sym2.inductionOn with
  | _ u v => simp

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicDualShift
