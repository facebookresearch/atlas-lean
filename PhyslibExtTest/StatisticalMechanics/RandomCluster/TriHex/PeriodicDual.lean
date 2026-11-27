/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicDual

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicDual`

* `triHexIndexEquiv` shifts the third direction: `(0, 2) ↦ (-triangularStep 0, 2)`, and fixes
  `(0, 0)`;
* `triangularEdgeChartEquiv` inverts the chart on the concrete edge `(0, 1)`;
* `triHexDualEdgeEquiv_chart` computes the dual of the edge `s(0, (1, 0))` as the hexagonal edge
  `s((0, false), ((1, 0), true))`;
* `triangular_edge_incident_faces` at the index `(0, 0)`: the origin lies on both incident faces.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicDual

open _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

-- The reindexing shifts the third direction and fixes the others.
example : triHexIndexEquiv (0, 2) = (-triangularStep 0, 2) := by
  simp [triHexIndexEquiv]

example : triHexIndexEquiv (0, 0) = (0, 0) := by
  simp [triHexIndexEquiv]

-- The chart equivalence inverts the edge chart on a concrete edge.
example : triangularEdgeChartEquiv.symm (triangularEdgeChart (0, 1)) = (0, 1) :=
  triangularEdgeChartEquiv.symm_apply_apply (0, 1)

-- The dual of the horizontal edge at the origin.
example : (triHexDualEdgeEquiv (triangularEdgeChart (0, 0)) : Sym2 HexVertex) =
    s(((0 : Site 2), false), (![1, 0], true)) := by
  rw [triHexDualEdgeEquiv_chart]
  simp [triHexIndexEquiv, hexagonalIndexedEdge, hexagonalStep]

-- The origin lies on both faces incident to the edge with index `(0, 0)`.
example : (0 : Site 2) ∈ triangularFace (incidentHexFaces (0, 0)).1 ∧
    (0 : Site 2) ∈ triangularFace (incidentHexFaces (0, 0)).2 :=
  ⟨(triangular_edge_incident_faces (0, 0)).1, (triangular_edge_incident_faces (0, 0)).2.2.1⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicDual
