/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorDisjointClusters

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorDisjointClusters`

In `Site 3`, with the empty configuration `⊥` and the three coordinate axes:
* `bc3_corridorClustersDisjoint_bot`: `bc3_CorridorClustersDisjoint` is satisfiable;
* `bc3_pairwiseSeparated_of_corridorClustersDisjoint` then gives pairwise separated mouths;
* `bc3_cluster_bot_singleton` at the unit ray point;
* `bc3_mouth_mem_clusterNbhd` and `bc3_corridorUnion_perm2` at explicit lengths.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorDisjointClusters

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- The empty configuration has disjoint corridor clusters along the three axes.
example : bc3_CorridorClustersDisjoint (⊥ : ConfigSpace (Sym2 (Site 3))) 0 1 2 1 2 3 :=
  bc3_corridorClustersDisjoint_bot (by decide) (by decide) (by decide) 1 2 3

-- Hence its corridor mouths are pairwise separated.
example : bc2_PairwiseSeparated (⊥ : ConfigSpace (Sym2 (Site 3))) 0 1 2 1 2 3 :=
  bc3_pairwiseSeparated_of_corridorClustersDisjoint _ _ _ _ _ _ _
    (bc3_corridorClustersDisjoint_bot (by decide) (by decide) (by decide) 1 2 3)

-- In the empty configuration the cut cluster of a nonzero site is a singleton.
example : cluster 3 (removeSite 0 (⊥ : ConfigSpace (Sym2 (Site 3)))) (hrHD_rayPt 0 1)
    = {hrHD_rayPt 0 1} :=
  bc3_cluster_bot_singleton _ (fun h => by simpa [hrHD_rayPt] using congrFun h 0)

-- The mouth lies in its cluster neighbourhood; corridor unions commute.
example : (hrHD_rayPt (0 : Fin 3) 1 : Site 3) ∈ bc3_clusterNbhd ⊥ 0 2 ∧
    bc3_corridorUnion (0 : Fin 3) 1 2 1 2 3 =
      hrHD_corridorEdges 1 (2 + 1) ∪ hrHD_corridorEdges 0 (1 + 1) ∪ hrHD_corridorEdges 2 (3 + 1) :=
  ⟨bc3_mouth_mem_clusterNbhd (by norm_num), bc3_corridorUnion_perm2 _ _ _ _ _ _⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorDisjointClusters
