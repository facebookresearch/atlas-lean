/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxOpenForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxOpenForest`

* `bst_Tcount_le_boundary_of_boxOpenForest` in conditional form;
* `bst_treeForestData_refutable_of_twoClusters` in conditional form;
* `bst_boxOpenForest_star` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxOpenForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- A box open forest gives the count bound.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : bst_BoxOpenForest ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bst_Tcount_le_boundary_of_boxOpenForest ω n h

-- Two disconnected trifurcations refute the tree-forest data.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {x y : Site d} (hxbox : x ∈ box d n)
    (hxtri : IsTrifurcation d ω x) (hybox : y ∈ box d n) (hytri : IsTrifurcation d ω y)
    (hsep : ¬ Connected d ω x y) :=
  bst_treeForestData_refutable_of_twoClusters ω n hxbox hxtri hybox hytri hsep

-- The star construction, by type.
example := @bst_boxOpenForest_star

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxOpenForest
