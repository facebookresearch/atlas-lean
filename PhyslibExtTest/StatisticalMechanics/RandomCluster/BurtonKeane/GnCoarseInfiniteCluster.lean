/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnCoarseInfiniteCluster

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnCoarseInfiniteCluster`

* `bc81_cut_cluster_infinite_of_coarse` on the coarse trifurcation of `bc60_upperLines` at the
  origin for `L = 3`: three arms with infinite clusters, pairwise separated by removing the box
  (instance).
* The first conjunct of `bc81_status` on the same coarse trifurcation (contracted-lattice
  separation).
* The fourth conjunct at `L = 3`: two upper-line sites stay connected in the two-box contracted
  graph after removing the origin.
* `bc81_coarseTrif_arms_connected_of_le_one` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GnCoarseInfiniteCluster

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- Three infinite arms of the upper-lines coarse trifurcation.
example : ∃ a₁ a₂ a₃ : Site 2,
    (cluster 2 bc60_upperLines a₁).Infinite ∧ (cluster 2 bc60_upperLines a₂).Infinite ∧
    (cluster 2 bc60_upperLines a₃).Infinite ∧
    (¬ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₁ a₂ ∧
     ¬ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₁ a₃ ∧
     ¬ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₂ a₃) :=
  bc81_cut_cluster_infinite_of_coarse _ 3 (bc61_wholeBox_severs_upperLines le_rfl)

-- The same arms are separated in the contracted lattice.
example : ∃ a₁ a₂ a₃ : Site 2,
    ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₁ a₂ ∧
    ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₁ a₃ ∧
    ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₂ a₃ :=
  bc81_status.1 _ 3 0 (bc61_wholeBox_severs_upperLines le_rfl)

-- In the two-box contracted graph the first and third upper lines stay connected.
example : ((bc76_twoBoxGn 3).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
    ⟨bc57_pt ((3 : ℕ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
    ⟨bc57_pt ((3 : ℕ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
  bc81_status.2.2.2.1 le_rfl

-- With at most one infinite cluster, the arms of a coarse trifurcation are connected.
example (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2)
    (hN : numInfiniteClusters 2 ω ≤ 1) (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site 2, Connected 2 ω a₁ a₂ ∧ Connected 2 ω a₁ a₃ ∧ Connected 2 ω a₂ a₃ ∧
      (¬ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) a₁ a₂ ∧
       ¬ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) a₁ a₃ ∧
       ¬ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) a₂ a₃) :=
  bc81_coarseTrif_arms_connected_of_le_one ω L hN h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GnCoarseInfiniteCluster
