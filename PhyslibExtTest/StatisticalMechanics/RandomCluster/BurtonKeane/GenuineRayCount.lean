/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineRayCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineRayCount`

* `bc88_upperLines_isTrifurcation_general`: the sites `(k, 1)` of the first upper line are
  trifurcations in the weak sense (instance).
* `bc88_upperLines_boxOpenForest_fails`: no box open forest exists for `bc60_upperLines`
  (refutation).
* The last conjunct of `bc88_status`: the origin is a coarse trifurcation for `L = 3`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineRayCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The site `(0, 1)` is a weak trifurcation of the upper-lines configuration.
example : IsTrifurcation 2 bc60_upperLines (bc57_pt 0 1) :=
  bc88_upperLines_isTrifurcation_general 0

-- No box open forest for the upper-lines configuration in `B_3`.
example : ¬ bst_BoxOpenForest bc60_upperLines 3 :=
  bc88_upperLines_boxOpenForest_fails (by norm_num)

-- The origin is a coarse trifurcation of the upper-lines configuration for `L = 3`.
example : bc61_IsCoarseTrifurcation bc60_upperLines 3 (0 : Site 2) :=
  bc88_status.2.2.2 3 le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineRayCount
