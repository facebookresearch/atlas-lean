/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount`

* non-vacuity: `flc2_SpanningTreeLeafCount` holds for the all-closed configuration of `ℤ²` at `n =
  1` (two distinct boundary sites, no trifurcation), via `flc2_spanningTreeLeafCount_of_noTrif`;
* `flc2_Tcount_le_boundary_of_spanningTree` applies to that witness;
* `flc2_tree_internal_lt_leaves` on the path on `Fin 3`, and the star witness `Flc2Witness.starG`
  has centre degree `3`;
* refutation: the certificate cannot hold for every configuration and `n ≥ 1` when `d ≥ 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

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

/-- The two boundary sites `(1, 0)` and `(1, 1)` of `B_1` in `ℤ²`. -/
def b₁ : Site 2 := ![1, 0]

/-- See `b₁`. -/
def b₂ : Site 2 := ![1, 1]

/-- `b₁` lies on the boundary of `B_1`. -/
theorem b₁_mem : b₁ ∈ vertexBoundary 2 1 := by
  simp only [mem_vertexBoundary, mem_box, b₁, Fin.forall_fin_two]
  decide

/-- `b₂` lies on the boundary of `B_1`. -/
theorem b₂_mem : b₂ ∈ vertexBoundary 2 1 := by
  simp only [mem_vertexBoundary, mem_box, b₂, Fin.forall_fin_two]
  decide

/-- The two boundary sites differ. -/
theorem b₁_ne_b₂ : b₁ ≠ b₂ := fun h => by simpa [b₁, b₂] using congrFun h 1
/-- The all-closed configuration of `ℤ²` has the spanning-tree certificate at `n = 1`. -/
theorem closed_cert : flc2_SpanningTreeLeafCount (d := 2) (fun _ => false) 1 :=
  flc2_spanningTreeLeafCount_of_noTrif _ 1 b₁_mem b₂_mem b₁_ne_b₂
    fun x _ => not_isTrifurcation_closed x

-- The counting bound applies to the witness.
example : Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  flc2_Tcount_le_boundary_of_spanningTree _ 1 closed_cert

-- Branch vertices are fewer than leaves in the path on `Fin 3`; the star has a degree-3 centre.
example : (Finset.univ.filter (fun v => 3 ≤ (SimpleGraph.pathGraph 3).degree v)).card
      < (Finset.univ.filter (fun v => (SimpleGraph.pathGraph 3).degree v = 1)).card ∧
    _root_.StatMech.Percolation.Flc2Witness.starG.degree 0 = 3 :=
  ⟨flc2_tree_internal_lt_leaves _ (SimpleGraph.isTree_pathGraph_add_one 2) (by simp),
    _root_.StatMech.Percolation.Flc2Witness.starG_centre_deg⟩

-- No such certificate holds for every configuration in dimension `d ≥ 1`.
example (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → flc2_SpanningTreeLeafCount ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    flc2_Tcount_le_boundary_of_spanningTree ω n (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount
