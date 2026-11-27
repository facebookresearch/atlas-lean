/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDistinctCutClusters

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDistinctCutClusters`

* `bc9_distinctCutClusters` holds unconditionally (checked at `n = 1`);
* its second conjunct on the all-closed configuration: no open edge joins distinct cut clusters;
* `bc9_threeArms_pairwiseNoMerge` used contrapositively: the all-closed configuration is not in
  `threeMeetBox d n`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDistinctCutClusters

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory

variable {d : ℕ}

/-- In the all-closed configuration every open cluster is a single site. -/
theorem cluster_closed (x : Site d) : cluster d (fun _ => false) x = {x} := by
  have hbot : openSubgraph d (fun _ => false) = ⊥ := by
    ext a b
    simp
  ext y
  simp only [mem_cluster, Connected, hbot, SimpleGraph.reachable_bot, Set.mem_singleton_iff]
  exact eq_comm

/-- In the all-closed configuration no site is a trifurcation. -/
theorem not_isTrifurcation_closed (x : Site d) :
    ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a₁, -, -, -, -, ⟨h, -, -⟩, -⟩
  rw [cluster_closed] at h
  exact h (Set.finite_singleton a₁)

/-- Removing a site from the all-closed configuration leaves it all-closed. -/
theorem removeSite_closed (x : Site d) : removeSite x (fun _ => false) = fun _ => false := by
  funext e
  simp only [removeSite, ite_self]

-- The distinct-cut-clusters statement holds at every scale.
example : bc9_DistinctCutClusters d 1 := bc9_distinctCutClusters 1

-- No open edge joins the distinct cut clusters `{x}` and `{y}` of the all-closed configuration.
example (x y : Site d) (hxy : x ≠ y) :
    ¬ IsOpenEdge d (removeSite 0 (fun _ => false)) x y :=
  (bc9_distinctCutClusters (d := d) 1).2 _ x y
    (by rw [removeSite_closed, cluster_closed, cluster_closed]; simpa using hxy)
    (self_mem_cluster _ x) (self_mem_cluster _ y)

-- The all-closed configuration does not have three infinite clusters meeting a box.
example (n : ℕ) : (fun _ => false) ∉ threeMeetBox d n := fun h => by
  obtain ⟨x₁, -, -, h1, -⟩ := bc9_threeArms_pairwiseNoMerge n _ h
  rw [removeSite_closed, cluster_closed] at h1
  exact h1 (Set.finite_singleton x₁)


/-! ## Diagnostics moved from the production module -/

-- The `#check` / `#print axioms` commands below were moved here from
-- `StatisticalMechanics/RandomCluster/BurtonKeane/ThreeDistinctCutClusters.lean`: diagnostics belong in tests, not in production modules.
#print axioms bc9_distinctCutClusters
#print axioms bc9_threeArms_pairwiseNoMerge

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDistinctCutClusters
