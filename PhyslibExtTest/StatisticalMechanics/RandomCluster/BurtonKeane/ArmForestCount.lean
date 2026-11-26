/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestCount`

* `bfk_star_count_witness`: one branch vertex, three leaves in the star;
* `bfk_forestCount` applied to the path graph on `Fin 2` with no branch vertex.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The star count witness.
example : Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card := bfk_star_count_witness

-- The forest count on the path with two vertices and an empty family of branch vertices.
example : Fintype.card (Fin 0) ≤ (Finset.univ : Finset (Fin 2)).card :=
  bfk_forestCount (SimpleGraph.pathGraph 2) (SimpleGraph.isAcyclic_pathGraph 2)
    (by decide) Fin.elim0 (fun a => a.elim0) (fun i => i.elim0) Finset.univ
    (fun v _ => Finset.mem_univ v)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestCount
