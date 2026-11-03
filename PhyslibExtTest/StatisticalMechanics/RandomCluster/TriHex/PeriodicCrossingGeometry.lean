/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicCrossingGeometry

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicCrossingGeometry`

With `e₀ = s(0, (1, 0))` the horizontal triangular edge at the origin and
`f₀ = s((0, false), ((1, 0), true))` its dual hexagonal edge:
* `triHexCanonicalPairedSegments_crossing` at index `(0, 0)`: the canonical segments meet;
* `triHexStraightEdge_crossing_iff_dual` (`←`): `e₀` and `f₀` cross;
* `triHexStraightEdge_crossing_iff_dual` (`→`, contrapositive): `e₀` does not cross the
  hexagonal edge `s(((5, 5), false), ((6, 5), true))`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicCrossingGeometry

open _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

/-- The horizontal triangular edge at the origin. -/
theorem tri_adj : triangularGraph.Adj 0 (0 + triangularStep 0) :=
  (SimpleGraph.mem_edgeSet _).1 (triangularIndexedEdge_mem (0, 0))

/-- The hexagonal edge from `(z, false)` in direction `0`. -/
theorem hex_adj (z : Site 2) : hexagonalGraph.Adj (z, false) (z + hexagonalStep 0, true) :=
  (SimpleGraph.mem_edgeSet _).1 (hexagonalIndexedEdge_mem (z, 0))

/-- The dual of the horizontal triangular edge at the origin. -/
theorem dual_zero : triHexDualEdgeEquiv ⟨s(0, 0 + triangularStep 0), tri_adj⟩ =
    ⟨s(((0 : Site 2), false), (0 + hexagonalStep 0, true)), hex_adj 0⟩ := by
  apply Subtype.ext
  exact (triHexDualEdgeEquiv_chart (0, 0)).trans (by simp [triHexIndexEquiv, hexagonalIndexedEdge])

-- The canonical paired segments at index `(0, 0)` meet.
example : ∃ t u : unitInterval,
    Path.segment (triangularPlaneVertex 0) (triangularPlaneVertex (0 + triangularStep 0)) t =
      Path.segment (hexagonalPlaneVertex ((triHexIndexEquiv (0, 0)).1, false))
        (hexagonalPlaneVertex
          ((triHexIndexEquiv (0, 0)).1 + hexagonalStep (triHexIndexEquiv (0, 0)).2, true)) u :=
  triHexCanonicalPairedSegments_crossing (0, 0)

-- Dual edges cross.
example : ∃ t u, triangularStraightEdgeArc tri_adj t = hexagonalStraightEdgeArc (hex_adj 0) u :=
  (triHexStraightEdge_crossing_iff_dual tri_adj (hex_adj 0)).2 dual_zero

-- A far-away hexagonal edge does not cross the triangular edge.
example : ¬ ∃ t u,
    triangularStraightEdgeArc tri_adj t = hexagonalStraightEdgeArc (hex_adj ![5, 5]) u := by
  rw [triHexStraightEdge_crossing_iff_dual, dual_zero]
  intro h
  have h' := congrArg Subtype.val h
  simp [funext_iff, Fin.forall_fin_two] at h'

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.PeriodicCrossingGeometry
