/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BadBox

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BadBox`

* `bc93_upperLines_witnesses_in_box` at `L = 3`;
* `bc93_no_badBox_of_le_one` and `bc93_two_le_numInfinite_of_badBox` in conditional form;
* `bc93_no_badBox_ae_of_uniqueness` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BadBox

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The upper-lines witnesses lie in the buffer box at `L = 3`.
example : bc57_pt (3 * ((3 : ℕ) : ℤ) + 1) 1 ∈ bc61_boxAround 2 3 (bc76_yBuf 3) :=
  (bc93_upperLines_witnesses_in_box le_rfl).1

-- At most one infinite cluster excludes bad boxes.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (hN : numInfiniteClusters d ω ≤ 1)
    (y' : Site d) : ¬ bc93_BadBox ω L y' :=
  bc93_no_badBox_of_le_one ω L hN y'

-- A bad box forces two infinite clusters.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y' : Site d} (h : bc93_BadBox ω L y') :
    2 ≤ numInfiniteClusters d ω :=
  bc93_two_le_numInfinite_of_badBox ω L h

-- Almost-sure uniqueness excludes bad boxes almost surely.
example := @bc93_no_badBox_ae_of_uniqueness

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BadBox
