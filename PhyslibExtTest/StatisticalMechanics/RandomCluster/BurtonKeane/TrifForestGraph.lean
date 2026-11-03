/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifForestGraph

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifForestGraph`

* non-vacuity: `bgc_TrifForestData` holds for the all-closed configuration of `ℤ²` at `R = 1`
  (`bgc_trifForestData_of_noTrif`), and gives the global contracted forest and the coarse count;
* `bgc_reach_of_openAdj_avoiding` on the one-edge configuration `ωe` (open edge `{(1, 0), (1, 1)}`)
  with the box around `(5, 5)`;
* `bgc_top_null_of_trifForest` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifForestGraph

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory
open scoped NNReal

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

/-- Removing sites from the all-closed configuration leaves it all-closed. -/
theorem removeSites_closed (T : Finset (Site d)) :
    removeSites T (fun _ => false) = fun _ => false := by
  funext e
  simp only [removeSites, ite_self]

/-- The all-closed configuration has no contracted-lattice trifurcation. -/
theorem not_gnTrif_closed (L : ℕ) (y : Site d) : ¬ bc67_IsGnTrifurcation (fun _ => false) L y := by
  rintro ⟨a, -, -, -, ⟨h, -, -⟩, -⟩
  rw [removeSites_closed, cluster_closed] at h
  exact h (Set.finite_singleton a)

/-- The all-closed configuration has no coarse trifurcation. -/
theorem not_coarseTrif_closed (L : ℕ) (y : Site d) :
    ¬ bc61_IsCoarseTrifurcation (fun _ => false) L y := by
  rintro ⟨a, -, -, -, -, -, ⟨h, -, -⟩, -⟩
  rw [removeSites_closed, cluster_closed] at h
  exact h (Set.finite_singleton a)

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

/-- The all-closed configuration has trifurcation forest data. -/
theorem closed_data (L : ℕ) : bgc_TrifForestData (d := 2) (fun _ => false) L 1 :=
  bgc_trifForestData_of_noTrif _ L 1 b₁_mem b₂_mem b₁_ne_b₂ fun y _ => not_gnTrif_closed L y

-- The data give the global contracted forest and the coarse count.
example (L : ℕ) : bc69_Gn_globalForest (d := 2) (fun _ => false) L 1 ∧
    bc61_coarseTcount (d := 2) (fun _ => false) L 1 ≤ boxSV_boundaryCard 2 1 :=
  ⟨bgc_globalForest_of_trifForestData _ L 1 (closed_data L),
    bgc_coarseTcount_of_trifForest _ L 1 (closed_data L)⟩

-- An open edge away from the removed box survives in the contracted lattice.
example : (bc67_contractedLattice ωe 1 ![5, 5]).Reachable b₁ b₂ :=
  bgc_reach_of_openAdj_avoiding ωe 1 _ _ _ ωe_adj
    (by simp [bc61_mem_boxAround, b₁, Fin.forall_fin_two])
    (by simp [bc61_mem_boxAround, b₂, Fin.forall_fin_two])

-- Data for every configuration would exclude `N = ∞` in `ℤ²`.
example (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bgc_top_null_of_trifForest p hp1 hp0 hdata

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifForestGraph
