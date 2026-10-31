/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.HexagonalTranslatedBoxes

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.HexagonalTranslatedBoxes`

* `hexagonalReflect` on a concrete vertex: `((1, 2), false) ↦ ((-1, -2), true)`;
* `hexagonalReflect_adj` transports the edge `(0, false) ~ ((1, 0), true)` to its reflection;
* `hexagonalTransBox_subset_double` with `x = 0 ∈ Λ_3`, `k = 1`;
* `hexagonalTransBox_activeBCMean_le` applied to the increasing shell-crossing event
  `hexagonalTransShellEvent 2 1 (0, false)` at `q = 1`, `β = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.HexagonalTranslatedBoxes

open _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

/-- The origin lies in `Λ_3`. -/
theorem zero_mem_box : (0 : Site 2) ∈ box 2 3 := by
  simp

-- The color-swapping reflection on a concrete vertex.
example : hexagonalReflect (![1, 2], false) = (![-1, -2], true) := by
  simp [hexagonalReflect]

-- The reflection of a hexagonal edge is a hexagonal edge.
example : hexagonalGraph.Adj (hexagonalReflect ((0 : Site 2), false))
    (hexagonalReflect (0 + hexagonalStep 0, true)) :=
  (hexagonalReflect_adj _ _).1 ((SimpleGraph.mem_edgeSet _).1 (hexagonalIndexedEdge_mem (0, 0)))

-- The translated box of radius `2 * 1` at the origin sits inside `Λ_6`.
example : hexagonalTransBox (2 * 1) 0 ⊆ box 2 (2 * 3) :=
  hexagonalTransBox_subset_double zero_mem_box (by norm_num)

-- Comparison of boundary conditions for the shell-crossing event.
example := hexagonalTransBox_activeBCMean_le (n := 3) (k := 1) (x := 0) zero_mem_box le_rfl
  (by norm_num) 1 1 le_rfl one_pos
  (hexagonalTransShellEvent_increasing (2 * 1) 1 ((0 : Site 2), false))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.HexagonalTranslatedBoxes
