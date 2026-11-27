/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmThroughPathCover

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmThroughPathCover`

* `bc116_ThroughPathCovered` holds for the path graph on `Fin 3` with boundary "not the middle
  vertex": the middle vertex lies inside the path `0 - 1 - 2` (non-vacuity);
* `bc116_leaf_on_boundary` applied to it: the leaf `0` is a boundary vertex;
* `bc116_armCovered_of_throughPathCovered` applied to it.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmThroughPathCover

open _root_.StatMech.Walls

/-- The middle vertex of the path on `Fin 3` is covered by a through path. -/
theorem path3_covered : bc116_ThroughPathCovered (SimpleGraph.pathGraph 3) (fun v => v ≠ 1)
    (fun _ => False) := by
  intro v hB _
  obtain rfl : v = 1 := not_not.mp hB
  exact ⟨0, 2, SimpleGraph.Walk.cons (show (SimpleGraph.pathGraph 3).Adj 0 1 by decide)
    (SimpleGraph.Walk.cons (show (SimpleGraph.pathGraph 3).Adj 1 2 by decide) .nil),
    by rw [SimpleGraph.Walk.isPath_def]; decide, by decide, by decide, by decide⟩

-- The leaf `0` lies in the boundary.
example : (0 : Fin 3) ≠ 1 :=
  bc116_leaf_on_boundary (SimpleGraph.pathGraph 3) path3_covered (fun _ h => h.elim)
    (by decide)

-- Through-path coverage gives arm coverage.
example : bc114_ArmCovered (SimpleGraph.pathGraph 3) (fun v => v ≠ 1) (fun _ => False) :=
  bc116_armCovered_of_throughPathCovered _ path3_covered

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmThroughPathCover
