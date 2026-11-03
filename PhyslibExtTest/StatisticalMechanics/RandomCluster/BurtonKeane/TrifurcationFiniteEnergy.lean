/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationFiniteEnergy

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationFiniteEnergy`

* `tfe_reachOrigin_iff_contact` on the all-closed configuration: neither condition holds (clusters
  are finite);
* `tfe_three_distinct_infinite_of_box` used contrapositively: the all-closed configuration is not in
  `threeMeetBox d n`;
* `tfe_threeMeetBox_of_top` and `tfe_routing_of_boxResidue` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationFiniteEnergy

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation
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

/-- Removing a site from the all-closed configuration leaves it all-closed. -/
theorem removeSite_closed (x : Site d) : removeSite x (fun _ => false) = fun _ => false := by
  funext e
  simp only [removeSite, ite_self]

/-- The all-closed configuration has no trifurcation contact. -/
theorem not_contact_closed : ¬ tfe_TrifurcationContact (d := d) (fun _ => false) := by
  rintro ⟨a₁, -, -, -, ⟨h, -, -⟩, -⟩
  rw [removeSite_closed, cluster_closed] at h
  exact h (Set.finite_singleton a₁)

-- So it does not satisfy the reach-origin condition either.
example : ¬ mco_ThreeClustersReachOrigin (d := d) (fun _ => false) :=
  fun h => not_contact_closed ((tfe_reachOrigin_iff_contact _).mp h)

-- The all-closed configuration is not in `threeMeetBox d n`.
example (n : ℕ) : (fun _ => false) ∉ threeMeetBox d n := fun h => by
  obtain ⟨x₁, -, -, -, ⟨h1, -⟩, -⟩ := tfe_three_distinct_infinite_of_box h
  rw [cluster_closed] at h1
  exact h1 (Set.finite_singleton x₁)

-- `N = ∞` meets some box in three distinct infinite clusters.
example (ω : ConfigSpace (Sym2 (Site d))) (htop : numInfiniteClusters d ω = ⊤) :
    ∃ n : ℕ, ω ∈ threeMeetBox d n :=
  tfe_threeMeetBox_of_top ω htop

-- The box residue gives disjoint routing.
example (n : ℕ) (h : tfe_BoxAttachResidue d n) : hrHD_DisjointRouting d n :=
  tfe_routing_of_boxResidue h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationFiniteEnergy
