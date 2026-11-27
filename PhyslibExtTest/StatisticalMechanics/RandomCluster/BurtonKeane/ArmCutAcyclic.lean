/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutAcyclic

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutAcyclic`

* `bc38_armAdjSpanning_of_noTrif` and `bc38_armCutGeometry_of_noTrif` hold for the all-closed
  configuration, which has no trifurcation;
* `bc38_Tcount_le_boundary_of_spanning_cutGeometry` applied to the all-closed configuration;
* `bc38_exists_rootedArmForest` applied to the all-closed configuration;
* `bc38_not_forall_spanning_cutGeometry`: the residues are refuted for `d = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutAcyclic

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

/-- The arm-adjacency spanning hypothesis for the all-closed configuration. -/
theorem span_closed (d n : ℕ) : bc38_ArmAdjSpanning (d := d) (fun _ => false) n :=
  bc38_armAdjSpanning_of_noTrif _ n fun x _ => noTrif_closed x

/-- The cut geometry for the all-closed configuration. -/
theorem geo_closed (d n : ℕ) : bc38_ArmCutGeometry (d := d) (fun _ => false) n :=
  bc38_armCutGeometry_of_noTrif _ n fun x _ => noTrif_closed x

-- The count bound for the all-closed configuration in `ℤ²`.
example : Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  bc38_Tcount_le_boundary_of_spanning_cutGeometry _ 1 le_rfl (span_closed 2 1) (geo_closed 2 1)

-- A rooted arm forest exists for the all-closed configuration.
example := bc38_exists_rootedArmForest (d := 2) (fun _ => false) 1 (span_closed 2 1)

-- The spanning and cut-geometry residues cannot hold for every configuration.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n →
    bc38_ArmAdjSpanning ω n ∧ bc38_ArmCutGeometry ω n :=
  bc38_not_forall_spanning_cutGeometry le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutAcyclic
