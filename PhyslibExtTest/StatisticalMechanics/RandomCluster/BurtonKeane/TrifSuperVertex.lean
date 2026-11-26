/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifSuperVertex

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifSuperVertex`

* instance: the origin of `bc60_upperLines` is a contracted-lattice trifurcation for `L = 3`
  (`bc67_upperLines_is_G_n_trifurcation`), hence a coarse trifurcation
  (`bc67_coarseTrif_is_G_n_trifurcation`), and the box severs heights `1` and `2`
  (`bc67_upperLines_Gn_severs`);
* `bc67_Gn_singleVertex_trifurcation_degree` on that instance;
* the all-closed configuration has no contracted-lattice trifurcation, and
  `bc67_contractedLattice_le` applies.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifSuperVertex

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


-- The origin of the upper-lines configuration is a contracted-lattice and a coarse trifurcation.
example : bc67_IsGnTrifurcation bc60_upperLines 3 (0 : Site 2) ∧
    bc61_IsCoarseTrifurcation bc60_upperLines 3 (0 : Site 2) :=
  ⟨bc67_upperLines_is_G_n_trifurcation le_rfl,
    (bc67_coarseTrif_is_G_n_trifurcation _ 3 0).mpr (bc67_upperLines_is_G_n_trifurcation le_rfl)⟩

-- Removing the box severs the lines at heights one and two.
example : ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable
    (bc57_pt ((3 : ℕ) + 1) 1) (bc57_pt ((3 : ℕ) + 1) 2) :=
  bc67_upperLines_Gn_severs le_rfl

-- The trifurcation has three incident, pairwise unreachable arms.
example : ∃ a₁ a₂ a₃ : Site 2,
    (bc67_GnIncident bc60_upperLines 3 0 a₁ ∧ bc67_GnIncident bc60_upperLines 3 0 a₂ ∧
      bc67_GnIncident bc60_upperLines 3 0 a₃) ∧
    (¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₁ a₂ ∧
     ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₁ a₃ ∧
     ¬ (bc67_contractedLattice bc60_upperLines 3 0).Reachable a₂ a₃) :=
  bc67_Gn_singleVertex_trifurcation_degree _ 3 0 (bc67_upperLines_is_G_n_trifurcation le_rfl)

-- The all-closed configuration has none; its contracted lattice lies in its open subgraph.
example (L : ℕ) (y : Site d) : ¬ bc67_IsGnTrifurcation (fun _ => false) L y ∧
    bc67_contractedLattice (fun _ => false) L y ≤ openSubgraph d (fun _ => false) :=
  ⟨not_gnTrif_closed L y, bc67_contractedLattice_le _ L y⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifSuperVertex
