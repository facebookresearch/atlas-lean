/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestRooting

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestRooting`

* `bc37_parentFunneling_of_noTrif` for the all-closed configuration, fed to
  `bc37_Tcount_le_boundary_of_parentFunneling` and, through
  `bc37_armForestRooting_iff_downArmSelector`, to a down-arm selector;
* `bc37_claw_funnelShadow_consistent` on explicit labels;
* `bc37_not_forall_parentFunneling`: parent funneling is refuted for `d = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestRooting

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

/-- Parent funneling for the all-closed configuration. -/
theorem pf_closed (d n : ℕ) : bc37_ParentFunneling (d := d) (fun _ => false) n :=
  bc37_parentFunneling_of_noTrif _ n fun x _ => noTrif_closed x

-- The count bound for the all-closed configuration.
example : Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  bc37_Tcount_le_boundary_of_parentFunneling _ 1 le_rfl (pf_closed 2 1)

-- A down-arm selector for the all-closed configuration.
example : bc37_DownArmSelector (d := 2) (fun _ => false) 1 :=
  (bc37_armForestRooting_iff_downArmSelector _ 1).mp
    (bc37_selfDownArm_of_parentFunneling _ 1 (pf_closed 2 1))

-- The claw funnel shadow is consistent for explicit labels.
example := bc37_claw_funnelShadow_consistent 0 1 (fun j => j.val + 2) 0 (by decide) (by decide)
  (by decide)

-- Parent funneling cannot hold for every configuration of `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → bc37_ParentFunneling ω n :=
  bc37_not_forall_parentFunneling le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestRooting
