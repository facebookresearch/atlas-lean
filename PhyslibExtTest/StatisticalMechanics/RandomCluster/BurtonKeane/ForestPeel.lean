/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel`

* `bkfl_arms_separate` in the all-closed configuration of `ℤ`: two distinct sites stay
  disconnected after removing any site (instance).
* In the all-closed configuration `bkfl_ForestPeel` holds, so `bkfl_existsPrivateArm_of_forestPeel`
  and `bkfl_Tcount_le_boundary_of_forestPeel` apply (non-vacuity).
* Forest peeling cannot hold for every configuration of `ℤ` (refutation through
  `tfc_not_forall_Tcount_le_boundary`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel

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

/-- The forest-peeling certificate holds in the all-closed configuration. -/
theorem closed_forestPeel (d n : ℕ) : bkfl_ForestPeel (d := d) (fun _ => false) n :=
  fun x _ hx => absurd hx (not_isTrifurcation_closed x)

-- Distinct arms stay separated: an instance where every arm is a single site.
example (x : Site 1) :
    ¬ Connected 1 (removeSite x (fun _ => false)) (fun _ => 1) (fun _ => 2) := by
  refine bkfl_arms_separate (a := fun _ => 1) (b := fun _ => 2) _ ?_ connected_rfl connected_rfl
  rw [removeSite_closed, connected_closed_iff]
  intro h; simpa using congrFun h 0

-- Private arms and the counting bound from forest peeling.
example : bkfl_ExistsPrivateArm (d := 2) (fun _ => false) 1 ∧
    Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  ⟨bkfl_existsPrivateArm_of_forestPeel _ 1 (closed_forestPeel 2 1),
    bkfl_Tcount_le_boundary_of_forestPeel _ 1 le_rfl (closed_forestPeel 2 1)⟩

-- No configuration-wide forest peeling exists in `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → bkfl_ForestPeel ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary le_rfl fun ω n hn =>
    bkfl_Tcount_le_boundary_of_forestPeel ω n hn (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
