/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BridgeThreeMeet

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BridgeThreeMeet`

* `bcl2_threeMeetBox_subset_top` at `n = 3`;
* `bcl2_bk_of_bridge` and `bcl2_hroute_of_bridge` in conditional form at `p = 1/2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BridgeThreeMeet

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls
open scoped NNReal

-- Three clusters meeting a box force infinitely many infinite clusters.
example : threeMeetBox 2 3 ⊆ {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} :=
  bcl2_threeMeetBox_subset_top 3

-- The bridge at `p = 1/2` gives the Burton–Keane conclusion.
example (hbridge : bcl2_Bridge (1 / 2 : ℝ≥0) (by norm_num)) :=
  bcl2_bk_of_bridge (1 / 2 : ℝ≥0) (by norm_num) (by norm_num) (by norm_num) hbridge

-- The bridge at `p = 1/2` gives the routing positivity.
example (hbridge : bcl2_Bridge (1 / 2 : ℝ≥0) (by norm_num)) :=
  bcl2_hroute_of_bridge (1 / 2 : ℝ≥0) (by norm_num) (by norm_num) (by norm_num) hbridge

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BridgeThreeMeet
