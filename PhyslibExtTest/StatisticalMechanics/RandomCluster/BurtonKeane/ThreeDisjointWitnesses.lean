/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDisjointWitnesses

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDisjointWitnesses`

* `bc2_threeWitnesses` holds unconditionally (checked at `n = 2`);
* `bc2_disjoint_of_ne` on the all-closed configuration: the clusters `{x}` and `{y}` of distinct
  sites are disjoint;
* `bc2_distinct_sites` used contrapositively: the all-closed configuration is not in `threeMeetBox d
  n`;
* `bc2_threeMeetBox_numInfinite` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDisjointWitnesses

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

-- The three-witness statement holds at every scale.
example : bc2_ThreeWitnesses d 2 := bc2_threeWitnesses 2

-- Distinct clusters are disjoint: the singletons of the all-closed configuration.
example (x y : Site d) (hxy : x ≠ y) :
    Disjoint (cluster d (fun _ => false) x) (cluster d (fun _ => false) y) :=
  bc2_disjoint_of_ne (by rw [cluster_closed, cluster_closed]; simpa using hxy)

-- The all-closed configuration does not have three infinite clusters meeting a box.
example (n : ℕ) : (fun _ => false) ∉ threeMeetBox d n := fun h => by
  obtain ⟨x₁, -, -, -, -, -, h1, -⟩ := bc2_distinct_sites n _ h
  rw [cluster_closed] at h1
  exact h1 (Set.finite_singleton x₁)

-- Three infinite clusters meeting a box force infinitely many infinite clusters.
example (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (hω : ω ∈ threeMeetBox d n) :
    numInfiniteClusters d ω = ⊤ :=
  bc2_threeMeetBox_numInfinite n ω hω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDisjointWitnesses
