/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedHubContraction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedHubContraction`

* instance: `bc112_separatedArmGraph_holds` gives `bc112_SeparatedArmGraph` for every configuration
  of `ℤ²` at `L = 3`, e.g. the all-closed one;
* non-vacuity: `bc112_BoundaryLeafResidue` holds for the all-closed configuration of `ℤ²` at `R =
  1`, via `bc112_boundaryLeafResidue_iff_full` and the separated contracted graph of that
  configuration;
* `bc112_separatedArmGraph_of_noTrif` and `bc112_separatedArmGraph_of_full` on the same witness.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedHubContraction

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

-- The separated arm graph exists for every planar configuration at `L = 3`.
example (R : ℕ) : bc112_SeparatedArmGraph (d := 2) (fun _ => false) 3 R :=
  bc112_separatedArmGraph_holds (by norm_num) _ 3 R le_rfl

-- The boundary-leaf residue holds for the all-closed configuration.
example (L : ℕ) : bc112_BoundaryLeafResidue (d := 2) (fun _ => false) L 1 :=
  (bc112_boundaryLeafResidue_iff_full _ L 1).mpr (closed_sepGraph L)

-- The arm graph from the absence of separated trifurcations and from the full graph.
example (L R : ℕ) : bc112_SeparatedArmGraph (d := d) (fun _ => false) L R :=
  bc112_separatedArmGraph_of_noTrif (z₀ := 0) _ L R fun y _ => not_sep_closed L y

-- The full separated contracted graph gives the arm graph.
example (L : ℕ) : bc112_SeparatedArmGraph (d := 2) (fun _ => false) L 1 :=
  bc112_separatedArmGraph_of_full _ L 1 (closed_sepGraph L)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedHubContraction
