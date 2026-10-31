/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeDisjointForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeDisjointForest`

* non-vacuity: `bc74_sublatticeForest_of_noTrif` for the all-closed configuration of `ℤ²` at `R =
  1`;
* `bc74_fiberForest_of_emptyFiber`: every fibre of the all-closed configuration has a fibre forest,
  and `bc74_fiber_count_of_fiberForest` applies;
* instance: `bc74_upperLines_sameResidue` at `L = 2`;
* `bc74_sublatticeForest_of_globalForest` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeDisjointForest

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

/-- The all-closed configuration has an empty coarse trifurcation set. -/
theorem coarseTrifFinset_closed (L R : ℕ) :
    bc61_coarseTrifFinset (d := d) (fun _ => false) L R = ∅ :=
  Finset.eq_empty_of_forall_notMem fun y hy =>
    not_coarseTrif_closed L y (bc61_mem_coarseTrifFinset.mp hy).2

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
-- The fibre bound for the all-closed configuration.
example (L : ℕ) : bc73_SublatticeForest (d := 2) (fun _ => false) L 1 :=
  bc74_sublatticeForest_of_noTrif _ L 1 b₁_mem b₂_mem b₁_ne_b₂ (coarseTrifFinset_closed L 1)

/-- Every fibre of the all-closed configuration is empty. -/
theorem fiber_closed (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1)) :
    bc73_fiber (d := 2) (fun _ => false) L R c = ∅ :=
  Finset.eq_empty_of_forall_notMem fun y hy =>
    not_gnTrif_closed L y (bc74_fiber_mem_gnTrif _ L R c hy)

-- Each fibre has a fibre forest, which bounds it.
example (L : ℕ) (c : Fin 2 → Fin (2 * L + 1)) :
    (bc73_fiber (d := 2) (fun _ => false) L 1 c).card ≤ boxSV_boundaryCard 2 1 :=
  bc74_fiber_count_of_fiberForest _ L 1 c
    (bc74_fiberForest_of_emptyFiber _ L 1 c (fiber_closed L 1 c) b₁_mem b₂_mem b₁_ne_b₂)

-- The origin and `(5, 0)` have the same residue modulo `5`.
example : bc73_resVec 2 (0 : Site 2) = bc73_resVec 2 (bc57_pt (2 * (2 : ℕ) + 1) 0) :=
  bc74_upperLines_sameResidue 2

-- A global contracted forest gives the fibre bound.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (h : bc69_Gn_globalForest ω L R) :
    bc73_SublatticeForest ω L R :=
  bc74_sublatticeForest_of_globalForest ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeDisjointForest
