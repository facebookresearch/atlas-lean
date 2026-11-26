/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BranchNeighbourArm

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BranchNeighbourArm`

* `bae_neighbour_of_reach` in the complete graph on `Fin 3`;
* `bae_fineTrifs_finite` for the all-open configuration of `ℤ²`;
* `bae_three_infinite_branches` and `bae_trif_arms` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BranchNeighbourArm

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- A reachable vertex is reached through a neighbour, avoiding the start.
example : ∃ n, (⊤ : SimpleGraph (Fin 3)).Adj 0 n ∧ ray34_AvoidReach ⊤ {0} n 1 :=
  bae_neighbour_of_reach ⊤ (by decide) (SimpleGraph.connected_top.preconnected 0 1)

-- Finitely many fine trifurcations in a box (all-open configuration).
example : {x : Site 2 | x ∈ box 2 3 ∧ bft_FineTrif (fun _ => true) x}.Finite :=
  bae_fineTrifs_finite _ 3

-- Branches and arms of fine trifurcations, by type.
example := @bae_three_infinite_branches
example := @bae_trif_arms

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BranchNeighbourArm
