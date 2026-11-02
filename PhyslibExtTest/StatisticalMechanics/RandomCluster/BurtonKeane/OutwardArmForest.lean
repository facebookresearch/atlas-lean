/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OutwardArmForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OutwardArmForest`

* concrete tree: `oaf_tree_not_forestPeel` on the ten-vertex tree `OafTree.G`, with degree checks
  by `decide` (root degree `3`, cut graph at the root has no edge at `0`);
* non-vacuity: `oaf_AbstractForestPeel` holds for `T = {0}` in the complete graph on `Fin 2`;
* refutation: `oaf_abstractForestPeel_false_of_rootCover` re-derives the failure on `OafTree.G`;
* `oaf_tree_internal_lt_leaves` applied to the path on `Fin 3`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OutwardArmForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

open _root_.StatMech.Percolation.OafTree in
-- The ten-vertex tree is a counterexample to abstract forest peeling.
example : ¬ oaf_AbstractForestPeel G Ttree := oaf_tree_not_forestPeel

open _root_.StatMech.Percolation.OafTree in
-- The root has degree three and is isolated in the cut graph.
example : G.degree 0 = 3 ∧ ∀ b, ¬ (oaf_cutGraph G 0).Adj 0 b := by
  refine ⟨by decide, fun b h => h.2.1 rfl⟩

-- Abstract forest peeling is satisfiable: a single vertex of `T` with an outside neighbour.
example : oaf_AbstractForestPeel (⊤ : SimpleGraph (Fin 2)) {0} := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  refine ⟨1, (SimpleGraph.top_adj 0 1 |>.mpr (by decide)).reachable, by decide, ?_⟩
  intro y hy hne
  exact absurd (Finset.mem_singleton.mp hy) hne

open _root_.StatMech.Percolation.OafTree in
-- The root-cover criterion re-derives the failure on the ten-vertex tree.
example : ¬ oaf_AbstractForestPeel G Ttree :=
  oaf_abstractForestPeel_false_of_rootCover G Ttree (r := 0) (c := child) (by decide)
    (by decide) (by decide) fun a _ ha => ⟨sub a, oaf_cover_leaf a ha⟩

-- Branch vertices are fewer than leaves in the path on `Fin 3`.
example : (Finset.univ.filter (fun v => 3 ≤ (SimpleGraph.pathGraph 3).degree v)).card
    < (Finset.univ.filter (fun v => (SimpleGraph.pathGraph 3).degree v = 1)).card :=
  oaf_tree_internal_lt_leaves _ (SimpleGraph.isTree_pathGraph_add_one 2) (by simp)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OutwardArmForest
