/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRootSide

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRootSide`

* `bc41_not_connected_removeSite_cutSite` for two explicit sites of `ℤ`;
* `bc41_parentFunneling_of_cutGeometryFixed'_arm` applied to the all-closed configuration (via
  `bc40_armCutGeometryFixed'_of_noTrif` and `bc41_rootSideComparableArm_of_noTrif`);
* `bc41_not_forall_rootWardAvoidingWalk`: refuted for `d = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRootSide

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The all-closed configuration has no trifurcation. -/
theorem noTrif_closed {d : ℕ} (x : Site d) : ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a₁, a₂, -, ⟨h₁₂, -, -⟩, ⟨c₁, c₂, -⟩, -⟩
  have hbot : openSubgraph d (fun _ => false) = ⊥ := by
    ext u v; simp
  unfold Connected at c₁ c₂
  rw [hbot, SimpleGraph.reachable_bot] at c₁ c₂
  exact h₁₂ (c₁.symm.trans c₂)

-- A site is never connected to the removed site.
example (ω : ConfigSpace (Sym2 (Site 1))) :
    ¬ Connected 1 (removeSite (Pi.single 0 1) ω) 0 (Pi.single 0 1) :=
  bc41_not_connected_removeSite_cutSite ω fun h => by simpa using congrFun h 0

-- Parent funneling for the all-closed configuration.
example : bc37_ParentFunneling (d := 2) (fun _ => false) 1 :=
  bc41_parentFunneling_of_cutGeometryFixed'_arm _ 1
    (bc40_armCutGeometryFixed'_of_noTrif _ 1 fun x _ => noTrif_closed x)
    (fun rank par => bc41_rootSideComparableArm_of_noTrif _ 1 rank par fun x _ => noTrif_closed x)

-- The root-ward avoiding walk hypotheses cannot hold for every configuration of `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n →
    bc40_ArmCutGeometryFixed' ω n ∧ ∀ (rank : Site 1 → ℕ ×ₗ ℕ) (par : Site 1 → Site 1),
      bc41_RootWardAvoidingWalk ω n rank par :=
  bc41_not_forall_rootWardAvoidingWalk le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRootSide
