/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint`

* `aed_sameComponent_of_commonLeaf` with a common leaf equal to both sites;
* `aed_globalForestArms_of_noTrif` for the all-closed configuration, fed to
  `aed_globalCutSeparation_of_globalForestArms` and `aed_Tcount_le_boundary_of_globalForestArms`;
* `aed_globalCutArmEnds_disjoint_of_distinct` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

/-- The all-closed configuration has no trifurcation. -/
theorem noTrif_closed {d : ℕ} (x : Site d) : ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a₁, a₂, -, ⟨h₁₂, -, -⟩, ⟨c₁, c₂, -⟩, -⟩
  have hbot : openSubgraph d (fun _ => false) = ⊥ := by
    ext u v; simp
  unfold Connected at c₁ c₂
  rw [hbot, SimpleGraph.reachable_bot] at c₁ c₂
  exact h₁₂ (c₁.symm.trans c₂)

-- A site shares its global component with itself.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    aed_sameGlobalComponent ∅ ω x x :=
  aed_sameComponent_of_commonLeaf ∅ ω (connected_refl _ x) (connected_refl _ x)

/-- Global forest arms for the all-closed configuration. -/
theorem arms_closed (d n : ℕ) : aed_GlobalForestArms (d := d) (fun _ => false) n :=
  aed_globalForestArms_of_noTrif _ n fun x _ => noTrif_closed x

-- Global cut separation for the all-closed configuration.
example : daep_GlobalCutSeparation (d := 2) (fun _ => false) 1 :=
  aed_globalCutSeparation_of_globalForestArms _ 1 (arms_closed 2 1)

-- The count bound for the all-closed configuration.
example : Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  aed_Tcount_le_boundary_of_globalForestArms _ 1 le_rfl (arms_closed 2 1)

-- Distinct global components have disjoint arm ends.
example {d : ℕ} (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {u v : Site d}
    (hdis : ¬ aed_sameGlobalComponent T ω u v) :
    Disjoint (daep_globalCutArmEnds T ω n u) (daep_globalCutArmEnds T ω n v) :=
  aed_globalCutArmEnds_disjoint_of_distinct T ω n hdis

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint
