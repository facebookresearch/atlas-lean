/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HallArmEnds

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HallArmEnds`

* `bhs_exists_injOn_of_hall` with singleton arm-end sets on `{0, 1, 2} ⊆ ℕ` (instance).
* In the all-closed configuration `daep_GlobalCutSeparation` holds, so
  `bhs_hallArmEnds_of_globalCutSeparation` gives `bhs_HallArmEnds`, and
  `bhs_distinctArmEnds_of_hall` and `bhs_Tcount_le_boundary_of_hall` apply (non-vacuity).
* Hall's condition cannot hold for every configuration of `ℤ` (refutation through
  `tfc_not_forall_Tcount_le_boundary`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.HallArmEnds

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

-- Hall's theorem with singleton arm-end sets.
example : ∃ φ : ℕ → ℕ, (∀ x ∈ ({0, 1, 2} : Finset ℕ), φ x ∈ ({x} : Finset ℕ)) ∧
    Set.InjOn φ ↑({0, 1, 2} : Finset ℕ) :=
  bhs_exists_injOn_of_hall _ (fun x => {x}) fun S _ => by
    rw [Finset.biUnion_singleton_eq_self]

/-- In the all-closed configuration every cluster is a single site, so no site is a
trifurcation. -/
theorem not_isTrifurcation_closed {d : ℕ} (x : Site d) :
    ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a, -, -, -, -, ⟨h, -, -⟩, -⟩
  have hb : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
  have hc : cluster d (fun _ => false) a = {a} := by
    ext y
    simp [cluster, Connected, hb, eq_comm]
  exact h (hc ▸ Set.finite_singleton a)

/-- Hall's condition in the all-closed configuration. -/
theorem closed_hall (d n : ℕ) (hn : 1 ≤ n) : bhs_HallArmEnds (d := d) (fun _ => false) n :=
  bhs_hallArmEnds_of_globalCutSeparation _ n hn
    ⟨id, fun x _ hx => absurd hx (not_isTrifurcation_closed x),
      fun x _ hx => absurd hx (not_isTrifurcation_closed x)⟩

-- Distinct arm ends and the counting bound in the all-closed configuration.
example : tfc_DistinctArmEnds (d := 2) (fun _ => false) 1 ∧
    Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  ⟨bhs_distinctArmEnds_of_hall _ 1 (closed_hall 2 1 le_rfl),
    bhs_Tcount_le_boundary_of_hall _ 1 (closed_hall 2 1 le_rfl)⟩

-- No configuration-wide Hall condition exists in `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → bhs_HallArmEnds ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary le_rfl fun ω n hn =>
    bhs_Tcount_le_boundary_of_hall ω n (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.HallArmEnds
