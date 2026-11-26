/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmFunnelParent

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmFunnelParent`

* `bc46_correctedParentGeometry_of_noTrif` for the all-closed configuration, fed to
  `bc46_parentFunneling_of_correctedParentGeometry`;
* the claw shadow: `bc46_clawShadow_hubCut_fails` and
  `bc46_clawShadow_correctedParentGeometry_ok`;
* `bc46_not_forall_armFunnelGeometry` and `bc46_not_forall_correctedParentGeometry` for `d = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmFunnelParent

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

-- Parent funneling for the all-closed configuration via the corrected parent geometry.
example : bc37_ParentFunneling (d := 2) (fun _ => false) 1 :=
  bc46_parentFunneling_of_correctedParentGeometry _ 1
    (bc46_correctedParentGeometry_of_noTrif _ 1 fun x _ => noTrif_closed x)

-- The hub cut fails on the claw shadow, while the corrected geometry holds there.
example := bc46_clawShadow_hubCut_fails
example := bc46_clawShadow_correctedParentGeometry_ok

-- The arm funnel geometry and the corrected parent geometry are refuted on `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → bc46_ArmFunnelGeometry ω n :=
  bc46_not_forall_armFunnelGeometry le_rfl
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n →
    bc46_CorrectedParentGeometry ω n :=
  bc46_not_forall_correctedParentGeometry le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmFunnelParent
