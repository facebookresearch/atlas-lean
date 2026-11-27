/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutSpanning

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutSpanning`

* `bc39_armAdjSpanning` for the all-open configuration;
* `bc39_Tcount_le_boundary_of_cutGeometryFixed` applied to the all-closed configuration (via
  `bc39_armCutGeometryFixed_of_noTrif`);
* `bc39_cutGeometryFixed_shadow_consistent` on explicit labels;
* `bc39_not_forall_cutGeometryFixed`: the fixed cut geometry is refuted for `d = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutSpanning

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

-- Arm adjacency spans for every configuration, e.g. the all-open one.
example : bc38_ArmAdjSpanning (d := 2) (fun _ => true) 1 := bc39_armAdjSpanning _ _

-- The count bound for the all-closed configuration.
example : Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  bc39_Tcount_le_boundary_of_cutGeometryFixed _ 1 le_rfl
    (bc39_armCutGeometryFixed_of_noTrif _ 1 fun x _ => noTrif_closed x)

-- The shadow of the fixed cut geometry is consistent for explicit labels.
example := bc39_cutGeometryFixed_shadow_consistent 1 2 0 (by decide) (by decide) (fun w => w = 1)
  (fun w hw => by omega)

-- The fixed cut geometry cannot hold for every configuration of `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n →
    bc39_ArmCutGeometryFixed ω n :=
  bc39_not_forall_cutGeometryFixed le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutSpanning
