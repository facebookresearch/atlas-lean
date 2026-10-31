/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxAllOpen

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxAllOpen`

* `bao_allOpen_not_frees_bridge` at `L = 1`: an all-open box does not make boxes internally
  connected (explicit configuration `bao_onlyBox0`);
* `bao_onlyBox0_allOpen` and `bao_bgn_idx_zero` at explicit sizes;
* `bao_box_internallyConnected` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxAllOpen

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- An all-open box need not free the bridge.
example : bff_BoxAllOpen (bao_onlyBox0 1) 1 ∧
    ¬ bsc_BoxesInternallyConnected (bao_onlyBox0 1) 1 (0 : Site 2) :=
  bao_allOpen_not_frees_bridge le_rfl

-- The explicit configuration opens the box, and the origin has index zero.
example : bff_BoxAllOpen (bao_onlyBox0 2) 2 := bao_onlyBox0_allOpen 2
example : bgn_idx 3 (0 : Site 2) = 0 := bao_bgn_idx_zero 3

-- An all-open trifurcation box is internally connected.
example (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (h : bao_AllOpenTrif ω L) {x y : Site 2}
    (hx : x ∈ box 2 L) (hy : y ∈ box 2 L) : Lattice.Connected 2 ω x y :=
  bao_box_internallyConnected h hx hy

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxAllOpen
