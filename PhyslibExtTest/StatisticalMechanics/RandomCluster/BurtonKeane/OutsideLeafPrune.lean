/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OutsideLeafPrune

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OutsideLeafPrune`

* `bc87_coarseTrif_arms_reach_outside` on the coarse trifurcation of `bc60_upperLines` at the
  origin for `L = 3`: three arms reach outside `B_10` (instance).
* The last conjunct of `bc87_status`: the upper-lines configuration has infinitely many infinite
  clusters.
* `bc87_pruning_preserves_branch_le_leaf` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OutsideLeafPrune

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- Three arms of the upper-lines coarse trifurcation reach outside `B_10`.
example : ∃ a₁ a₂ a₃ : Site 2,
    (∃ z, z ∉ box 2 10 ∧ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₁ z) ∧
    (∃ z, z ∉ box 2 10 ∧ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₂ z) ∧
    (∃ z, z ∉ box 2 10 ∧ Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines) a₃ z) :=
  bc87_coarseTrif_arms_reach_outside _ 3 (bc61_wholeBox_severs_upperLines le_rfl) 10

-- The upper-lines configuration has infinitely many infinite clusters.
example : numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc87_status.2.2.2.2

-- Pruned forests keep the branch–leaf inequality against the boundary.
example (R : ℕ) {S : Set (Site 2)} [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj] (hacyc : G.IsAcyclic)
    (hmin : ∀ v : (↑S : Type), 1 ≤ G.degree v)
    (hbdry : ∀ v : (↑S : Type), G.degree v = 1 → (v : Site 2) ∈ vertexBoundary 2 R) :
    (Finset.univ.filter (fun v : (↑S : Type) => 3 ≤ G.degree v)).card ≤ boxSV_boundaryCard 2 R :=
  bc87_pruning_preserves_branch_le_leaf R G hacyc hmin hbdry

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OutsideLeafPrune
