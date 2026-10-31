/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.CoarseGeometry

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.CoarseGeometry`

* `triangularGraph_connected` gives reachability of the concrete site `(5, -3)` from `0`;
* `triangular_dist_le_coordinate_sum` bounds `d_tri(0, (2, 1)) ≤ 3`;
* `triangular_dist_le_two_mul_of_sub_mem_box` bounds `d_tri(0, (1, -1)) ≤ 2` from
  `(1, -1) ∈ box 2 1`;
* `hexToTriAnchor` unfolds on a white vertex, and
  `hexagonal_dist_le_four_mul_add_two_of_anchor_sub_mem_box` gives `d_hex((e₀, true), (0, false))
  ≤ 2` for two vertices with the same anchor (`n = 0`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.CoarseGeometry

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.Lattice

-- The triangular lattice connects `0` to `(5, -3)`.
example : triangularGraph.Reachable 0 ![5, -3] :=
  triangularGraph_connected.preconnected _ _

-- The `ℓ¹` bound at `(2, 1)`.
example : triangularGraph.dist 0 ![2, 1] ≤ 3 := by
  simpa using triangular_dist_le_coordinate_sum 0 ![2, 1]

-- The box bound at `(1, -1) ∈ box 2 1`.
example : triangularGraph.dist 0 ![1, -1] ≤ 2 := by
  have h : (![1, -1] : Site 2) - 0 ∈ box 2 1 := by
    intro i
    fin_cases i <;> decide
  simpa using triangular_dist_le_two_mul_of_sub_mem_box h

-- The anchor of a white vertex is shifted by the first hexagonal step.
example (x : Site 2) : hexToTriAnchor (x, true) = x - hexagonalStep 0 := rfl

-- Two hexagonal vertices with the same anchor are at distance at most `2`.
example : hexagonalGraph.dist ((hexagonalStep 0 : Site 2), true) (0, false) ≤ 2 := by
  have h : hexToTriAnchor (0, false) - hexToTriAnchor ((hexagonalStep 0 : Site 2), true) ∈
      box 2 0 := by
    intro i
    simp [hexToTriAnchor]
  simpa using hexagonal_dist_le_four_mul_add_two_of_anchor_sub_mem_box h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.CoarseGeometry
