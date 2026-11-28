/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryPruning

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryPruning`

* `bpr_not_forall_treeForest`: tree-forest data are refuted for `d = 1`;
* `bpr_Tcount_le_boundary_of_treeForest` in conditional form;
* `bpr_treeForestData_slh_refutable` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryPruning

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Tree-forest data cannot hold for every configuration of `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → bpr_TreeForestData ω n :=
  bpr_not_forall_treeForest le_rfl

-- Tree-forest data give the count bound.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : bpr_TreeForestData ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bpr_Tcount_le_boundary_of_treeForest ω n h

-- A trifurcation in the box refutes the strong tree-forest data.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Site d) (hxbox : x ∈ box d n)
    (htri : IsTrifurcation d ω x) : ¬ slh_TreeForestData ω n :=
  bpr_treeForestData_slh_refutable ω n x hxbox htri

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryPruning
