/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorMouth

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorMouth`

In the plane, along the axis-`0` corridor of length `4` (all-closed configuration):
* `bc_mouthCorridor_reaches_farEnd`: the mouth reaches the far end;
* `bc_mouthCorridor_step_open` at step `2`;
* `bc_corridorCell_ne_origin` and `bc_farEnd_ne_neighbour` at explicit values.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorMouth

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

-- The mouth reaches the far end of the corridor.
example : Connected 2 (bc_mouthCutConfig 0 3 closed2) (hrHD_rayPt 0 1)
    (hrHD_rayPt 0 (((3 : ℕ) : ℤ) + 1)) :=
  bc_mouthCorridor_reaches_farEnd closed2 0 3

-- The corridor step from distance `2` to `3` is open.
example : IsOpenEdge 2 (bc_mouthCutConfig 0 3 closed2) (hrHD_rayPt 0 ((2 : ℕ) : ℤ))
    (hrHD_rayPt 0 (((2 : ℕ) : ℤ) + 1)) :=
  bc_mouthCorridor_step_open closed2 0 3 2 (by norm_num) (by norm_num)

-- Corridor cells avoid the origin, and the far end differs from the mouth.
example : (hrHD_rayPt (0 : Fin 2) ((2 : ℕ) : ℤ) : Site 2) ≠ 0 ∧
    (hrHD_rayPt (0 : Fin 2) (((3 : ℕ) : ℤ) + 1) : Site 2) ≠ hrHD_rayPt 0 1 :=
  ⟨bc_corridorCell_ne_origin 0 2 (by norm_num), bc_farEnd_ne_neighbour 0 3 (by norm_num)⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorMouth
