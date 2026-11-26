/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmDivergenceRank

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmDivergenceRank`

* `bc28_globalForestArms_of_rootedArmDivergence` and
  `bc28_Tcount_le_boundary_of_rootedArmDivergence` applied to the all-closed configuration
  (rooted arm divergence via `rfp_rootedArmDivergence_of_noTrif`);
* `bc28_rootedArmDivergence_iff_existsRankDivergence` used in the forward direction on the
  all-closed configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmDivergenceRank

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

/-- Rooted arm divergence for the all-closed configuration. -/
theorem div_closed (d n : ℕ) : rfp_RootedArmDivergence (d := d) (fun _ => false) n :=
  rfp_rootedArmDivergence_of_noTrif _ n fun x _ => noTrif_closed x

-- The global forest arms for the all-closed configuration.
example : aed_GlobalForestArms (d := 2) (fun _ => false) 1 :=
  bc28_globalForestArms_of_rootedArmDivergence _ 1 (div_closed 2 1)

-- The count bound for the all-closed configuration.
example : Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  bc28_Tcount_le_boundary_of_rootedArmDivergence _ 1 le_rfl (div_closed 2 1)

-- A divergence rank exists for the all-closed configuration.
example := (bc28_rootedArmDivergence_iff_existsRankDivergence (d := 2) (fun _ => false) 1).mp
  (div_closed 2 1)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmDivergenceRank
