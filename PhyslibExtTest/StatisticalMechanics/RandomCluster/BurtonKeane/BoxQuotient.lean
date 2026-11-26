/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxQuotient

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxQuotient`

* `bc72_upperLines_deg3` and `bc72_upperLines_arm_adjacent` at `L = 3` (explicit upper-lines
  configuration);
* `bc72_collapseBox_center` and `bc72_y_mem_box` at explicit sites;
* `bc72_count_of_multiBox` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxQuotient

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The collapsed box has degree at least three in the quotient (upper lines).
example := bc72_upperLines_deg3 (L := 3) le_rfl

-- The super-vertex has an arm neighbour in the quotient (upper lines).
example : ∃ a : Site 2,
    (bc72_quotGraph (openSubgraph 2 bc60_upperLines) (bc72_collapseBox 3 (0 : Site 2))).Adj 0 a :=
  bc72_upperLines_arm_adjacent le_rfl

-- The centre lies in its box and collapses to itself.
example : (0 : Site 2) ∈ bc61_boxAround 2 3 0 := bc72_y_mem_box 3 0
example : bc72_collapseBox 3 (0 : Site 2) 0 = 0 := bc72_collapseBox_center 3 0

-- A multi-box forest on the quotient gives the coarse count.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (h : bc72_MultiBoxForestOnQuot ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc72_count_of_multiBox ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxQuotient
