/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalTrifArms

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalTrifArms`

* `bc47_isTrifurcation_fakeConfig` and `bc47_not_classical_fakeConfig`: an explicit
  trifurcation that is not classical;
* `bc47_arc_residue_fails_on_fakeConfig` at `n = 2`;
* `bc47_isTrifurcation_of_classical` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalTrifArms

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The fake configuration has a trifurcation at `bc47_x` that is not classical.
example : IsTrifurcation 2 bc47_fakeConfig bc47_x := bc47_isTrifurcation_fakeConfig
example : ¬ bc47_IsClassicalTrifurcation bc47_fakeConfig bc47_x := bc47_not_classical_fakeConfig

-- The remove-site arm residue fails on the fake configuration.
example : ¬ arc_TrifArmsRemoveSiteInfinite bc47_fakeConfig 2 :=
  bc47_arc_residue_fails_on_fakeConfig 2

-- Classical trifurcations are trifurcations.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : bc47_IsClassicalTrifurcation ω x) : IsTrifurcation d ω x :=
  bc47_isTrifurcation_of_classical ω x h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalTrifArms
