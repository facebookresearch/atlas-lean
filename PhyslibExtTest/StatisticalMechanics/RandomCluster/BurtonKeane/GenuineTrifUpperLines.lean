/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifUpperLines

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifUpperLines`

* `bc83_upperLines_genuineTrif_at_zero`: the origin is a contracted-lattice trifurcation of
  `bc60_upperLines` for `L = 3` (instance), and `bc83_genuineTrif_iff_coarse` turns it into a
  coarse trifurcation.
* `bc83_no_overcount` (first conjunct of `bc83_status`): the two counts agree.
* `bc83_genuine_count_le_boundary_of_forest` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifUpperLines

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The origin is a trifurcation of the upper-lines configuration for `L = 3`.
example : bc83_genuineTrif bc60_upperLines 3 (0 : Site 2) :=
  bc83_upperLines_genuineTrif_at_zero le_rfl

-- ... and therefore a coarse trifurcation.
example : bc61_IsCoarseTrifurcation bc60_upperLines 4 (0 : Site 2) :=
  (bc83_genuineTrif_iff_coarse _ _ _).mp (bc83_upperLines_genuineTrif_at_zero (by norm_num))

-- The contracted-lattice and coarse counts agree.
example : bc83_genuineTrifCount bc60_upperLines 3 2 = bc61_coarseTcount bc60_upperLines 3 2 :=
  bc83_status.1 _ 3 2

-- A coarse forest bounds the count.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (h : bc61_CoarseForestLeafCount ω L R) :
    bc83_genuineTrifCount ω L R ≤ boxSV_boundaryCard 2 R :=
  bc83_genuine_count_le_boundary_of_forest ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifUpperLines
