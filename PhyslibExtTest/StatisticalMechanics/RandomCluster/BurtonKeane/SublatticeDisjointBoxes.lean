/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeDisjointBoxes

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeDisjointBoxes`

* concrete sublattice: `(3, -6)` lies on `3ℤ²` (`bc73_onSublattice 1`, by `decide`), and
  `bc73_sublattice_boxes_disjoint` makes the `1`-boxes around `0` and `(3, 0)` disjoint;
* `bc73_sameResidue_boxes_disjoint` for `(1, 0)` and `(4, 3)` at `L = 1` (same residue, by
  `decide`);
* non-vacuity: `bc73_SublatticeForest` holds for the all-closed configuration
  (`bc73_sublatticeForest_of_noTrif`), and `bc73_covering` applies to it;
* the density limit `bc73_const_boundary_vol_tendsto` in `ℤ¹`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeDisjointBoxes

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


-- A site of the sublattice `3ℤ²`.
example : bc73_onSublattice 1 (![3, -6] : Site 2) := by decide

-- Boxes around distinct sublattice sites are disjoint.
example : Disjoint (bc61_boxAround 2 1 (0 : Site 2)) (bc61_boxAround 2 1 ![3, 0]) :=
  bc73_sublattice_boxes_disjoint (by decide) (by decide) (by decide)

-- Boxes around distinct sites with the same residue are disjoint.
example : Disjoint (bc61_boxAround 2 1 (![1, 0] : Site 2)) (bc61_boxAround 2 1 ![4, 3]) :=
  bc73_sameResidue_boxes_disjoint (by decide) (by decide)

-- The all-closed configuration has the fibre bound, hence the covering bound.
example (L R : ℕ) : bc61_coarseTcount (d := d) (fun _ => false) L R
    ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R :=
  bc73_covering _ L R (bc73_sublatticeForest_of_noTrif _ L R (coarseTrifFinset_closed L R))

-- The fibre bound has vanishing density in `ℤ¹`.
example (L : ℕ) : Filter.Tendsto (fun R => (((2 * L + 1) ^ 1 * boxSV_boundaryCard 1 R : ℕ) : ℝ)
    / ((boxFinsetBK 1 R).card : ℝ)) Filter.atTop (nhds 0) :=
  bc73_const_boundary_vol_tendsto 1 le_rfl L

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeDisjointBoxes
