/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRay

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRay`

* `bar_center_not_adj` and `bar_center_reach_eq`: the centre is isolated in the contracted
  lattice (instance at the all-open configuration of `ℤ²`);
* `bar_armRay_of_infiniteComponent` and `bar_bk_uniqueness_of_trifData` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRay

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls
open scoped NNReal

-- The centre has no neighbour in the contracted lattice (all-open configuration).
example (z : Site 2) : ¬ (bc67_contractedLattice (fun _ => true) 3 0).Adj 0 z :=
  bar_center_not_adj _ 3 0 z

-- The centre reaches only itself.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {x z : Site d}
    (h : (bc67_contractedLattice ω L x).Reachable x z) : z = x :=
  bar_center_reach_eq ω L h

-- An infinite component outside the box gives an arm ray.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :=
  bar_armRay_of_infiniteComponent ω L y a hinf

-- Trifurcation forest data everywhere gives the Burton–Keane conclusion.
example := @bar_bk_uniqueness_of_trifData

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRay
