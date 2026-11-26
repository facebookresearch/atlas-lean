/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationConstruction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationConstruction`

* `removeSite_forceOpen_eq`: forcing the edge `{0, y}` and removing the origin is removing the
  origin; `removeSite_le` applied to the all-closed configuration;
* `exists_three_distinct` on `Set.univ : Set ℕ` (infinite `encard`);
* the all-closed configuration lies neither in `threeMeetBox d n` nor in any `NeighborTrifPrecursor`
  (its clusters are finite);
* `trif_pos_of_precursor_pos` and `iEqTop_subset_iUnion_threeMeetBox` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationConstruction

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

-- Forcing an edge at the origin is invisible after removing the origin.
example (y : Site d) :
    removeSite 0 (forceOpenFinset {s(0, y)} (fun _ => false)) = fun _ => false := by
  rw [removeSite_forceOpen_eq 0 _ (by simp), removeSite_closed]

-- Removing a site only closes edges.
example (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) : removeSite x ω ≤ ω := removeSite_le x ω

-- An infinite set has three distinct elements.
example : ∃ a b c : ℕ, a ∈ Set.univ ∧ b ∈ Set.univ ∧ c ∈ Set.univ ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c :=
  exists_three_distinct (Set.encard_eq_top_iff.mpr Set.infinite_univ)

-- The all-closed configuration has no three infinite clusters and no precursor.
example (n : ℕ) (a₁ a₂ a₃ : Site d) : (fun _ => false) ∉ threeMeetBox d n ∧
    (fun _ => false) ∉ NeighborTrifPrecursor d a₁ a₂ a₃ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨-, x, -, -, -, -, -, hx, -⟩
    rw [cluster_closed] at hx
    exact hx (Set.finite_singleton x)
  · rintro ⟨-, -, ⟨h, -, -⟩, -⟩
    rw [removeSite_closed, cluster_closed] at h
    exact h (Set.finite_singleton a₁)

-- A positive-probability precursor gives a positive-probability trifurcation.
example (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (a₁ a₂ a₃ : Site d)
    (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) : 0 < μ {ω | IsTrifurcation d ω 0} :=
  trif_pos_of_precursor_pos μ hfe a₁ a₂ a₃ hpos

-- `N = ∞` is covered by the events `threeMeetBox d n`.
example (ω : ConfigSpace (Sym2 (Site d))) (h : numInfiniteClusters d ω = ⊤) :
    ∃ n, ω ∈ threeMeetBox d n := by
  simpa only [Set.mem_iUnion] using iEqTop_subset_iUnion_threeMeetBox (d := d) h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationConstruction
