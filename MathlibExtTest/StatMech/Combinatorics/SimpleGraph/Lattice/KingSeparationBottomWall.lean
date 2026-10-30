/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationBottomWall

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationBottomWall`

* `ewt_fjord_nonvacuous`; `ewt_kingRowLinked_of_fourThin` instantiated with `ksd_stair`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationBottomWall

example : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    ewt_BottomWallThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ewt_fjord_nonvacuous

example : mci_KingRowLinked ksd_stair (![1, 1] : Site 2) :=
  ewt_kingRowLinked_of_fourThin ksd_stair ksd_mem_interior_11 ksd_stair_fourThin
    ewt_ksd_bottomWallThick

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationBottomWall
