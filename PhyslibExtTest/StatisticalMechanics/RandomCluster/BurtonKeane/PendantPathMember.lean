/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PendantPathMember

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PendantPathMember`

* `bc118_degreeOnePendant_not_covered` on the path on `Fin 2`: its end `1` is a degree-one vertex
  that is neither boundary nor hub;
* `bc118_concrete_interiorPendant_not_covered` and `bc118_pathUnion_can_have_pendant` (instances);
* the forest inequality of `bc118_membership_NOT_needed_for_count` on the path on `Fin 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PendantPathMember

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- A degree-one vertex off the boundary is not covered by through paths.
example : ¬ bc116_ThroughPathCovered (SimpleGraph.pathGraph 2) (fun w => w = 0) (fun _ => False) :=
  bc118_degreeOnePendant_not_covered (v := 1) _ (by decide) (by decide) (by simp)

-- The library's concrete pendant witness.
example : ¬ bc116_ThroughPathCovered (SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)})
    (fun w => w = 0) (fun _ => False) :=
  bc118_concrete_interiorPendant_not_covered

-- Unions of paths can have pendants.
example : ∃ (F' : SimpleGraph (Fin 3)) (_ : DecidableRel F'.Adj) (v : Fin 3),
    F'.degree v = 1 ∧ ¬ bc114_IsInternal F' v :=
  bc118_pathUnion_can_have_pendant

-- The branch–leaf inequality on the path on `Fin 2`.
example : (Finset.univ.filter (fun v => 3 ≤ (SimpleGraph.pathGraph 2).degree v)).card
    ≤ (Finset.univ.filter (fun v => (SimpleGraph.pathGraph 2).degree v = 1)).card :=
  (bc118_membership_NOT_needed_for_count (d := 1) (fun _ => false) 0 0).2 _
    (SimpleGraph.isTree_pathGraph_add_one 1).isAcyclic (by decide)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PendantPathMember
