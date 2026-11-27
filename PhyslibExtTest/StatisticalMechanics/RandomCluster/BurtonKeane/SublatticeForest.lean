/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeForest`

* non-vacuity: `bc73_SublatticeForest` holds for the all-closed configuration of `ℤ²` at `R = 1`
  (two distinct boundary sites, no contracted-lattice trifurcation), via
  `bc108_sublatticeForest_of_noTrif`;
* `bc108_full_covering_of_globalForest` and `bc108_separatedCount_le_of_globalForest` in conditional
  form;
* the fibre bound of `bc108_status` applied to the all-closed configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

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
-- The all-closed configuration has the sublattice fibre bound.
example (L : ℕ) : bc73_SublatticeForest (d := 2) (fun _ => false) L 1 :=
  bc108_sublatticeForest_of_noTrif _ L 1 b₁_mem b₂_mem b₁_ne_b₂ fun y _ => not_gnTrif_closed L y

-- A global contracted forest bounds the coarse count and the separated count.
example (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R ∧
      bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R :=
  ⟨bc108_full_covering_of_globalForest ω L R h, bc108_separatedCount_le_of_globalForest ω L R h⟩

-- Each residue fibre is bounded by the coarse count.
example (L R : ℕ) (c : Fin d → Fin (2 * L + 1)) :
    (bc73_fiber (fun _ => false) L R c).card ≤ bc61_coarseTcount (d := d) (fun _ => false) L R :=
  bc108_status.2.1 _ L R c

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeForest
