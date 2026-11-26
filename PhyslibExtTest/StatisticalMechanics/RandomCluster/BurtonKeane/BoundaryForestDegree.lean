/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryForestDegree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryForestDegree`

* `bc113_bForest_acyclic` for the complete graph on `Fin 3` with boundary `{0}`;
* `bc113_no_boundaryAnchored_on_triangle`: no boundary-anchored forest on the triangle;
* `bc113_boundaryAnchored_nonvacuous`: one exists on `Fin 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryForestDegree

open _root_.StatMech.Walls

/-- Every vertex of the triangle reaches `0`. -/
theorem tri_reaches : bc113_ReachesB (⊤ : SimpleGraph (Fin 3)) (fun v => v = 0) :=
  fun v => ⟨0, rfl, SimpleGraph.connected_top.preconnected v 0⟩

-- The parent forest of the triangle towards `0` is acyclic.
example : (bc113_bForest (⊤ : SimpleGraph (Fin 3)) (fun v => v = 0) tri_reaches).IsAcyclic :=
  bc113_bForest_acyclic _ _ tri_reaches

-- No boundary-anchored forest on the triangle with boundary `{0}`.
example := bc113_no_boundaryAnchored_on_triangle

-- A boundary-anchored forest exists on `Fin 2`.
example := bc113_boundaryAnchored_nonvacuous

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryForestDegree
