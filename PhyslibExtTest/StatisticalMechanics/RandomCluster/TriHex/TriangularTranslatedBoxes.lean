/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TriangularTranslatedBoxes

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TriangularTranslatedBoxes`

With `x = 0 ∈ Λ_3` and `k = 1` (so `2k < 3`):
* `triangularTransBox_subset_double`: the box of radius `2` sits inside `Λ_6`;
* the center of a translated box of radius `2` is not on its boundary;
* `triangularTransBox_outer_margin`: the center is not on the outer shell of `Λ_6`;
* `triangularTransBox_activeBCMean_le` applied to the increasing shell-crossing event
  `triangularTransShellEvent 2 1 0` at `q = 1`, `β = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TriangularTranslatedBoxes

open _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

/-- The origin lies in `Λ_3`. -/
theorem zero_mem_box : (0 : Site 2) ∈ box 2 3 := by
  simp

-- The translated box of radius `2 * 1` at the origin sits inside `Λ_6`.
example : triangularTransBox (2 * 1) 0 ⊆ box 2 (2 * 3) :=
  triangularTransBox_subset_double zero_mem_box (by norm_num)

-- The center is an interior vertex of the translated box.
example (x : Site 2) : ¬ triangularTransBoxBoundary 2 x (triangularTransBoxCenter 2 x) := by
  simp [triangularTransBoxBoundary, triangularTransBoxCenter]

-- The center of the sub-box is away from the outer boundary of `Λ_6`.
open scoped Classical in
example : triangularTransBoxIncl (triangularTransBox_subset_double zero_mem_box (by norm_num))
      (triangularTransBoxCenter (2 * 1) 0) ∉ triangularBoxShell (2 * 3) (2 * 3) :=
  triangularTransBox_outer_margin zero_mem_box (by norm_num) _

-- Comparison of boundary conditions for the shell-crossing event.
example := triangularTransBox_activeBCMean_le (n := 3) (k := 1) (x := 0) zero_mem_box le_rfl
  (by norm_num) 1 1 le_rfl one_pos (triangularTransShellEvent_increasing (2 * 1) 1 0)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TriangularTranslatedBoxes
