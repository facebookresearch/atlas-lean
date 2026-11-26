/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmInjectionCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmInjectionCount`

* `bc50_countBound_of_noTrif` for the all-closed configuration, fed to
  `bc50_injection_iff_countBound`;
* the finite shadows `bc50_armEndpoint_map_not_injective` and `bc50_abstract_injection_exists`;
* `bc50_burton_keane_bernoulli_of_armForest_routingCover` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmInjectionCount

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

-- The classical boundary arm injection for the all-closed configuration.
example : bc48_ClassicalBoundaryArmInjection (d := 2) (fun _ => false) 1 :=
  (bc50_injection_iff_countBound _ 1).mpr
    (bc50_countBound_of_noTrif _ 1 fun x _ => noTrif_closed x)

-- The arm-endpoint shadow map is not injective, but an abstract injection exists.
example : bc50_shadowArmEnd 0 0 = bc50_shadowArmEnd 1 0 := bc50_armEndpoint_map_not_injective.1
example := bc50_abstract_injection_exists

-- The routing-cover Burton–Keane route, by type.
example := @bc50_burton_keane_bernoulli_of_armForest_routingCover

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmInjectionCount
