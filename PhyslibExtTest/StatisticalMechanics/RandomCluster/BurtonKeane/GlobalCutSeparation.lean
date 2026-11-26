/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation`

* `daep_cutArmEnds_disjoint_of_disconnected` in the all-closed configuration of `ℤ` (instance).
* In the all-closed configuration `daep_GlobalCutSeparation` holds, so
  `daep_cutDisjoint_of_globalCutSeparation` and `daep_Tcount_le_boundary_of_globalCutSeparation`
  apply (non-vacuity).
* Global cut separation cannot hold for every configuration of `ℤ` (refutation through
  `tfc_not_forall_Tcount_le_boundary`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

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

/-- In the all-closed configuration, connection means equality. -/
theorem connected_closed_iff {d : ℕ} (x y : Site d) :
    Connected d (fun _ => false) x y ↔ x = y := by
  have hb : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
  simp [Connected, hb]

/-- Removing a site from the all-closed configuration changes nothing. -/
theorem removeSite_closed {d : ℕ} (x : Site d) :
    removeSite x (fun _ => false) = fun _ => false :=
  funext fun e => by unfold removeSite; split_ifs <;> rfl

-- Arm ends of two distinct sites are disjoint in the all-closed configuration.
example (x : Site 1) : Disjoint (daep_cutArmEnds (fun _ => false) 1 x (fun _ => 1))
    (daep_cutArmEnds (fun _ => false) 1 x (fun _ => -1)) := by
  refine daep_cutArmEnds_disjoint_of_disconnected _ 1 ?_
  rw [removeSite_closed, connected_closed_iff]
  intro h; simpa using congrFun h 0

/-- Global cut separation in the all-closed configuration. -/
theorem closed_globalCutSeparation (d n : ℕ) :
    daep_GlobalCutSeparation (d := d) (fun _ => false) n :=
  ⟨id, fun x _ hx => absurd hx (not_isTrifurcation_closed x),
    fun x _ hx => absurd hx (not_isTrifurcation_closed x)⟩

-- Disjoint cut arm ends and the counting bound in the all-closed configuration.
example : daep_CutDisjointArmEnds (d := 2) (fun _ => false) 2 ∧
    Tcount 2 (fun _ => false) 2 ≤ boxSV_boundaryCard 2 2 :=
  ⟨daep_cutDisjoint_of_globalCutSeparation _ 2 (by norm_num) (closed_globalCutSeparation 2 2),
    daep_Tcount_le_boundary_of_globalCutSeparation _ 2 (by norm_num)
      (closed_globalCutSeparation 2 2)⟩

-- No configuration-wide global cut separation exists in `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → daep_GlobalCutSeparation ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary le_rfl fun ω n hn =>
    daep_Tcount_le_boundary_of_globalCutSeparation ω n hn (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
