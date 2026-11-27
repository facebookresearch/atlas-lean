/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootDepthWalk

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootDepthWalk`

* `bc45_armDepthRank_injective` and `bc45_rootWardRootParent_holds_at_depthRank` hold for every
  configuration; checked on the all-closed configuration;
* the chain and Y-tree shadows `bc45_chainShadow_confirms`, `bc45_yTreeShadow_confirms`, and the
  concrete values `bc45_chainPar 2 = 1`, `bc45_yDep 3 = 2` by `decide`;
* refutation: `bc40_ArmCutGeometryFixed'` cannot hold for every configuration and `n ≥ 1` when `d ≥
  1` (via `bc45_selfDownArm_of_cutGeometryFixed'` and the self-down-arm count).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootDepthWalk

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

variable {d : ℕ}

-- The depth rank and the root-ward condition at it, on the all-closed configuration.
example (n : ℕ) : bc43_RootWardRootParent (d := d) (fun _ => false) n
    (bc45_armDepthRank (fun _ => false) n) (bc45_armForestPar (fun _ => false) n) :=
  bc45_rootWardRootParent_holds_at_depthRank _ n

-- The depth rank separates connected trifurcations, in any configuration.
example (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (a b : Site d) (ha : a ∈ box d n)
    (hta : IsTrifurcation d ω a) (hb : b ∈ box d n) (htb : IsTrifurcation d ω b) (hab : a ≠ b)
    (hc : Connected d ω a b) : bc45_armDepthRank ω n a ≠ bc45_armDepthRank ω n b :=
  bc45_armDepthRank_injective ω n a ha hta b hb htb hab hc

-- The small shadows of the depth construction, with concrete values.
example : bc45_chainPar 2 = 1 ∧ bc45_yDep 3 = 2 ∧ bc45_yPar 3 = 1 ∧
    bc45_chainDep 1 < bc45_chainDep 2 :=
  ⟨by decide, by decide, bc45_yTreeShadow_confirms.2.2.1.2, bc45_chainShadow_confirms.2.1.1⟩

-- Fixed cut geometry cannot hold for every configuration in dimension `d ≥ 1`.
example (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc36_Tcount_le_boundary_of_selfDownArm ω n hn
      (bc45_selfDownArm_of_cutGeometryFixed' ω n (h ω n hn))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RootDepthWalk
