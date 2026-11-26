/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalHarmBox

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalHarmBox`

* `bc53_harmbox_false`: arms of trifurcations in a box need not stay in the box;
* the explicit witness: `Bc53Witness.bwall_isTrifurcation` and `Bc53Witness.bwall_arm_outside_box`;
* `Bc53Witness.threeRay_canonical_origin`: the three-ray configuration is canonical at the origin;
* `bc53_harmbox_succ`: arms stay in the next box (all-open configuration).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalHarmBox

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- Arms of trifurcations need not stay in the box.
example := bc53_harmbox_false

-- The explicit trifurcation whose arm leaves the box.
example : IsTrifurcation 2 Bc53Witness.bwallConfig (![(1 : ℤ), 0] : Site 2) :=
  Bc53Witness.bwall_isTrifurcation
example : (![(2 : ℤ), 0] : Site 2) ∉ box 2 1 := Bc53Witness.bwall_arm_outside_box

-- The three-ray configuration has a canonical trifurcation at the origin.
example : IsCanonicalTrifurcation 2 CtcWitness.threeRayConfig (CtcWitness.px 0) :=
  Bc53Witness.threeRay_canonical_origin

-- Arms stay in the next box (all-open configuration).
example := bc53_harmbox_succ (d := 2) (fun _ => true) 3

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalHarmBox
