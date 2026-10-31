/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedPathChain

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedPathChain`

In the plane, along the axis-`0` corridor of length `4` (all-closed configuration):
* `bc2_forcedPathConn_farEnd`: after forcing and removing the origin, the mouth reaches the far
  end;
* `bc2_forcedPathConn` at distance `3`;
* `bc2_corridorChain_one_step` and `bc2_corridorStep` at explicit steps.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedPathChain

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal
open _root_.StatMech.Percolation.DisjointPaths

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

-- The mouth reaches the far end of the forced corridor.
example : Connected 2 (removeSite 0 (forceOpenFinset (hrHD_corridorEdges (0 : Fin 2) (3 + 1))
    closed2)) (hrHD_rayPt 0 1) (hrHD_rayPt 0 (((3 : ℕ) : ℤ) + 1)) :=
  bc2_forcedPathConn_farEnd closed2 0 3

-- And every intermediate cell.
example : Connected 2 (removeSite 0 (forceOpenFinset (hrHD_corridorEdges (0 : Fin 2) (3 + 1))
    closed2)) (hrHD_rayPt 0 1) (hrHD_rayPt 0 ((3 : ℕ) : ℤ)) :=
  bc2_forcedPathConn closed2 0 3 3 (by norm_num) (by norm_num)

-- The first and the third corridor steps.
example : CorridorStep (hrHD_corridorEdges (0 : Fin 2) (3 + 1)) (hrHD_rayPt 0 1) (hrHD_rayPt 0 2) ∧
    CorridorStep (hrHD_corridorEdges (0 : Fin 2) (3 + 1)) (hrHD_rayPt 0 ((3 : ℕ) : ℤ))
      (hrHD_rayPt 0 (((3 : ℕ) : ℤ) + 1)) :=
  ⟨bc2_corridorChain_one_step 0 3 (by norm_num), bc2_corridorStep 0 3 3 (by norm_num) le_rfl⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedPathChain
