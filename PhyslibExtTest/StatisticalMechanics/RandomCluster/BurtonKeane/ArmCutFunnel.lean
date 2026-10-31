/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutFunnel

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutFunnel`

* `bc40_armCutGeometryFixed'_of_noTrif` and `bc40_rootSideComparable_of_noTrif` hold for the
  all-closed configuration;
* `bc40_Tcount_le_boundary_of_cutGeometryFixed'` applied to the all-closed configuration;
* `bc40_chainShadow_consistent` and `bc40_chainShadow_universalFunnel_false` (finite shadows);
* `bc40_not_forall_cutGeometryFixed'`: the hypotheses are refuted for `d = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutFunnel

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

-- The count bound for the all-closed configuration in `ℤ²`.
example : Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  bc40_Tcount_le_boundary_of_cutGeometryFixed' _ 1 le_rfl
    (bc40_armCutGeometryFixed'_of_noTrif _ 1 fun x _ => noTrif_closed x)
    (fun rank par => bc40_rootSideComparable_of_noTrif _ 1 rank par fun x _ => noTrif_closed x)

-- The six-site chain shadow is consistent.
example := bc40_chainShadow_consistent

-- The universal funnel fails on the chain shadow.
example := bc40_chainShadow_universalFunnel_false

-- The fixed cut geometry with root-side comparability cannot hold for every configuration.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n →
    bc40_ArmCutGeometryFixed' ω n ∧ ∀ (rank : Site 1 → ℕ ×ₗ ℕ) (par : Site 1 → Site 1),
      bc40_RootSideComparable ω n rank par :=
  bc40_not_forall_cutGeometryFixed' le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutFunnel
