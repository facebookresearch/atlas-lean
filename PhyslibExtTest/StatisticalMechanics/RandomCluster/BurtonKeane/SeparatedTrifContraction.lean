/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedTrifContraction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedTrifContraction`

* non-vacuity: `bc106_SeparatedContractedTrifGraph` holds for the all-closed configuration of `ℤ²`
  at `R = 1` (`bc106_separatedContractedTrifGraph_of_noTrif`), and
  `bc106_separatedCount_of_contractedGraph` applies to it;
* `bc106_origin_event_eq`: the all-closed configuration has no separated coarse trifurcation at the
  origin;
* `bc106_boxes_disjoint` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedTrifContraction

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
/-- The all-closed configuration has no separated coarse trifurcation. -/
theorem not_sep_closed (L : ℕ) (y : Site d) : ¬ bc106_SeparatedCoarseTrif (fun _ => false) L y :=
  fun h => not_coarseTrif_closed L y (bc106_isCoarseTrif_of_separated h)

/-- The all-closed configuration of `ℤ²` has a separated contracted graph at `R = 1`. -/
theorem closed_sepGraph (L : ℕ) :
    bc106_SeparatedContractedTrifGraph (d := 2) (fun _ => false) L 1 :=
  bc106_separatedContractedTrifGraph_of_noTrif _ L 1 b₁_mem b₂_mem b₁_ne_b₂
    fun y _ => not_sep_closed L y

-- The separated count is bounded by the boundary for the witness.
example (L : ℕ) : bc106_separatedTcount (d := 2) (fun _ => false) L 1 ≤ boxSV_boundaryCard 2 1 :=
  bc106_separatedCount_of_contractedGraph _ L 1 (closed_sepGraph L)

-- At the origin, separated and coarse trifurcations agree; neither occurs when all is closed.
example (L : ℕ) : ¬ bc106_SeparatedCoarseTrif (d := d) (fun _ => false) L 0 :=
  fun h => not_coarseTrif_closed L 0 ((bc106_origin_event_eq _ L).mp h)

-- Boxes of distinct separated coarse trifurcations are disjoint.
example (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y z : Site d)
    (hy : bc106_SeparatedCoarseTrif ω L y) (hz : bc106_SeparatedCoarseTrif ω L z) (hne : y ≠ z) :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L z) :=
  bc106_boxes_disjoint hy hz hne

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedTrifContraction
