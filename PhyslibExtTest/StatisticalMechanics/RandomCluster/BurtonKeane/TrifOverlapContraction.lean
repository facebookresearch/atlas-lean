/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifOverlapContraction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifOverlapContraction`

* `bc105_boxes_overlap_of_close_centres` for the centres `(1, 0)` and `0` at `L = 1`;
* `bc105_boxes_overlap_of_adjacent_centres` in `ℤ¹`;
* non-vacuity: `bc105_contractedTrifGraph_of_noTrif` and `bc105_count_of_noTrif` for the all-closed
  configuration of `ℤ²` at `R = 1`;
* `bc105_adversary_box_overlap` at `z = (1, 1)`, `L = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifOverlapContraction

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
-- Boxes around close centres overlap.
example : (0 : Site 2) ∈ bc61_boxAround 2 1 ![1, 0] ∧ (0 : Site 2) ∈ bc61_boxAround 2 1 0 :=
  bc105_boxes_overlap_of_close_centres (by simp [Fin.forall_fin_two])

-- In `ℤ¹` every centre has a distinct neighbour whose box overlaps its own.
example (z : Site 1) : ∃ y : Site 1, y ≠ z ∧ z ∈ bc61_boxAround 1 1 y ∧
    z ∈ bc61_boxAround 1 1 z ∧ y ∈ bc61_boxAround 1 1 y ∧ y ∈ bc61_boxAround 1 1 z :=
  bc105_boxes_overlap_of_adjacent_centres le_rfl le_rfl z

-- The all-closed configuration has the contracted graph and a zero-cost count.
example (L : ℕ) : bc103_ContractedTrifGraph (d := 2) (fun _ => false) L 1 ∧
    bc61_coarseTcount (d := 2) (fun _ => false) L 1 ≤ boxSV_boundaryCard 2 1 :=
  ⟨bc105_contractedTrifGraph_of_noTrif _ L 1 b₁_mem b₂_mem b₁_ne_b₂
      fun y _ => not_gnTrif_closed L y,
    bc105_count_of_noTrif _ L 1 b₁_mem b₂_mem b₁_ne_b₂ fun y _ => not_gnTrif_closed L y⟩

-- The adversary's boxes around `0` and `(1, 1)` overlap.
example : (0 : Site 2) ∈ bc61_boxAround 2 1 0 ∧ (![1, 1] : Site 2) ∈ bc61_boxAround 2 1 0 ∧
    (![1, 1] : Site 2) ∈ bc61_boxAround 2 1 ![1, 1] :=
  bc105_adversary_box_overlap (by simp [Fin.forall_fin_two])

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifOverlapContraction
