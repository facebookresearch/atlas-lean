/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorStepOpen

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorStepOpen`

In the plane, with the all-closed configuration:
* `bkm_dcc_step_open_eq_true`: forcing the edge `(1,0)–(2,0)` keeps it open after removing the
  origin;
* the same for a two-edge forced set.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorStepOpen

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- `(1,0)` and `(2,0)` are lattice neighbours. -/
theorem adj10 : (hypercubicLattice 2).Adj ![1, 0] ![2, 0] := by
  simp [hypercubicLattice, NearestNeighbour, Fin.sum_univ_two]

/-- The edge `(1,0)–(2,0)` avoids the origin. -/
theorem notMem10 : (0 : Site 2) ∉ s(![1, 0], ![2, 0]) := by
  simp only [Sym2.mem_iff, not_or]
  constructor <;> intro h <;> simpa using congrFun h 0

-- A forced edge avoiding the origin is open after removing the origin.
example : removeSite 0 (forceOpenFinset {s(![1, 0], ![2, 0])} closed2) s(![1, 0], ![2, 0]) = true :=
  bkm_dcc_step_open_eq_true closed2 _ (Finset.mem_singleton_self _) notMem10

-- The same edge inside a larger forced set.
example : removeSite 0 (forceOpenFinset {s(0, ![1, 0]), s(![1, 0], ![2, 0])} closed2)
    s(![1, 0], ![2, 0]) = true :=
  bkm_dcc_step_open_eq_true closed2 _ (by simp) notMem10

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorStepOpen
