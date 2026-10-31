/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RemoveSitePosition

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RemoveSitePosition`

* `bxp_notConnected_removeSite` on the all-closed configuration (distinct sites stay disconnected);
* the all-closed configuration lies neither in `bxp_Y` nor in any `bxp_tripleEvent` (its clusters
  are finite);
* `bxp_threeMeetBox_subset_iUnion` applied, and `bxp_exists_triple_pos` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RemoveSitePosition

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open MeasureTheory
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

-- Distinct sites are disconnected in the all-closed configuration, also after removing the origin.
example (a b : Site d) (hab : a ≠ b) : ¬ Connected d (removeSite 0 (fun _ => false)) a b :=
  bxp_notConnected_removeSite _ fun h => hab ((cluster_closed a ▸ mem_cluster.mpr h :
    b ∈ ({a} : Set (Site d)))).symm

-- The all-closed configuration is not in `bxp_Y`.
example : (fun _ => false) ∉ bxp_Y := by
  rintro ⟨-, ⟨h, -, -⟩, -⟩
  rw [cluster_closed] at h
  exact h (Set.finite_singleton _)

-- Nor in any triple event.
example (n : ℕ) (x y z : Site d) : (fun _ => false) ∉ bxp_tripleEvent d n x y z := by
  rintro ⟨-, -, -, -, h, -⟩
  rw [cluster_closed] at h
  exact h (Set.finite_singleton _)

-- Three clusters meeting a box lie in some triple event.
example (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (h : ω ∈ threeMeetBox d n) :
    ∃ x y z, ω ∈ bxp_tripleEvent d n x y z := by
  simpa only [Set.mem_iUnion] using bxp_threeMeetBox_subset_iUnion d n h

-- Positive probability of `N = ∞` gives a triple event of positive probability.
example (p : ℝ≥0) (hp1 : p ≤ 1)
    (htop : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      {ω | numInfiniteClusters d ω = ⊤}) :
    ∃ (n : ℕ) (x y z : Site d),
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bxp_tripleEvent d n x y z) :=
  bxp_exists_triple_pos p hp1 htop

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RemoveSitePosition
