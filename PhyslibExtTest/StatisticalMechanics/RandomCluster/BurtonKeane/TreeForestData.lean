/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TreeForestData

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TreeForestData`

* non-vacuity: `slh_TreeForestData` holds for `ωe`, the configuration of `ℤ²` whose only open edge
  joins the boundary sites `(1, 0)` and `(1, 1)` of `B_1` (no trifurcation), via
  `slh_treeForestData_of_noTrif`;
* `slh_spanningTreeLeafCount_of_treeForest` and `slh_Tcount_le_boundary_of_treeForest` apply to it;
* refutation: the certificate cannot hold for every configuration and `n ≥ 1` when `d ≥ 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TreeForestData

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

/-- The two boundary sites `(1, 0)` and `(1, 1)` of `B_1` in `ℤ²`. -/
def b₁ : Site 2 := ![1, 0]

/-- See `b₁`. -/
def b₂ : Site 2 := ![1, 1]

/-- The configuration in `ℤ²` whose only open edge is `{b₁, b₂}`. -/
noncomputable def ωe : ConfigSpace (Sym2 (Site 2)) := fun e => decide (e = s(b₁, b₂))

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

/-- The edge `{b₁, b₂}` is open in `ωe`. -/
theorem ωe_adj : (openSubgraph 2 ωe).Adj b₁ b₂ := by
  refine ⟨?_, by simp [ωe]⟩
  simp [hypercubicLattice_adj, Fin.sum_univ_two, b₁, b₂]

/-- Every site of a nontrivial open path of `ωe` is `b₁` or `b₂`. -/
theorem ωe_cluster_subset (x : Site 2) : cluster 2 ωe x ⊆ {x, b₁, b₂} := by
  rintro y ⟨p⟩
  cases p.reverse with
  | nil => exact Or.inl rfl
  | cons h _ =>
    have h2 := h.2
    simp only [ωe, decide_eq_true_eq, Sym2.eq_iff] at h2
    rcases h2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- `ωe` has no trifurcation. -/
theorem ωe_not_trif (x : Site 2) : ¬ IsTrifurcation 2 ωe x := by
  rintro ⟨a, -, -, -, -, ⟨h, -, -⟩, -⟩
  exact h ((Set.toFinite {a, b₁, b₂}).subset (ωe_cluster_subset a))

/-- The one-edge configuration carries tree forest data. -/
theorem ωe_cert : slh_TreeForestData ωe 1 :=
  slh_treeForestData_of_noTrif ωe 1 b₁_mem b₂_mem ωe_adj fun x _ => ωe_not_trif x

-- Tree forest data give the spanning-tree certificate.
example : flc2_SpanningTreeLeafCount ωe 1 := slh_spanningTreeLeafCount_of_treeForest ωe 1 ωe_cert

-- The counting bound applies.
example : Tcount 2 ωe 1 ≤ boxSV_boundaryCard 2 1 :=
  slh_Tcount_le_boundary_of_treeForest ωe 1 ωe_cert

-- No such certificate holds for every configuration in dimension `d ≥ 1`.
example {d : ℕ} (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → slh_TreeForestData ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    slh_Tcount_le_boundary_of_treeForest ω n (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TreeForestData
