/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct`

* `bk2_card_le_of_pairwiseDisjoint` on explicit finsets (`{0, 1}` injected into `{0, 1, 2}`);
* `bk2_disjointArmEnds_of_subsingleton` for the all-closed configuration, fed to
  `bk2_Tcount_le_boundary_of_disjointArmEnds`;
* `bk2_not_forall_disjointArmEnds`: disjoint arm ends are refuted for `d = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct

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

-- Pairwise disjoint nonempty subsets give the card bound (explicit instance).
example : ({0, 1} : Finset ℕ).card ≤ ({0, 1, 2} : Finset ℕ).card :=
  bk2_card_le_of_pairwiseDisjoint {0, 1} {0, 1, 2} (fun x => {x}) (by decide) (by decide)
    (by decide)

/-- Disjoint arm ends for the all-closed configuration. -/
theorem disj_closed (d n : ℕ) : bk2_DisjointArmEnds (d := d) (fun _ => false) n :=
  bk2_disjointArmEnds_of_subsingleton _ n fun x _ _ hx => (noTrif_closed x hx).elim

-- The count bound for the all-closed configuration.
example : Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  bk2_Tcount_le_boundary_of_disjointArmEnds _ 1 le_rfl (disj_closed 2 1)

-- Disjoint arm ends cannot hold for every configuration of `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → bk2_DisjointArmEnds ω n :=
  bk2_not_forall_disjointArmEnds le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct
