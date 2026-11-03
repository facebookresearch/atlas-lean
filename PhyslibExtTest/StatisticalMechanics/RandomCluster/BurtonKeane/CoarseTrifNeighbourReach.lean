/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifNeighbourReach

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifNeighbourReach`

On the even-lines configuration `bc57_evenLines`:
* refutations: `¬ bc56_BoxClusterReachesNbr 2 6` and `¬ bmm_BoxMengerAttachment 2 6`;
* it lies in `threeMeetBox 2 6` and has `N = ⊤`;
* the clusters at heights `0` and `2` differ, and the height-`2` cluster does not reach a
  neighbour of the origin;
* `bc57_pt_adj` at the origin.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifNeighbourReach

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- Box cluster neighbour reach fails at radius `6`.
example : ¬ bc56_BoxClusterReachesNbr 2 6 :=
  bc57_boxClusterReachesNbr_false

-- Box Menger attachment fails at radius `6`.
example : ¬ bmm_BoxMengerAttachment 2 6 :=
  bc57_status.2.1

-- The even lines meet the radius-6 box in three infinite clusters and have `N = ⊤`.
example : bc57_evenLines ∈ threeMeetBox 2 6 ∧ numInfiniteClusters 2 bc57_evenLines = ⊤ :=
  ⟨bc57_mem_threeMeetBox, bc57_numInfiniteClusters_top⟩

-- Distinct even lines give distinct clusters; the line at height `2` misses the origin's
-- neighbours.
example : cluster 2 bc57_evenLines (bc57_pt 0 (2 * 0)) ≠
      cluster 2 bc57_evenLines (bc57_pt 0 (2 * 1)) ∧
    ¬ bc56_ClusterReachesNbr bc57_evenLines (bc57_pt 0 (2 * 1)) :=
  ⟨bc57_cluster_ne (by norm_num), bc57_no_reachesNbr (by norm_num)⟩

-- Horizontal neighbours are adjacent.
example : (hypercubicLattice 2).Adj (bc57_pt 0 0) (bc57_pt (0 + 1) 0) :=
  bc57_pt_adj 0 0

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifNeighbourReach
