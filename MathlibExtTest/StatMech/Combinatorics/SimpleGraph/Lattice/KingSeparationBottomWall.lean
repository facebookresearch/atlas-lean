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

* `ewt_fjord_nonvacuous`; the staircase `ksd_stair` is king row-linked from `(1, 1)`
  via `ksc_kingRowLinked_of_noKingSeparation` and `ksc_ksd_noKingSeparation`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationBottomWall

example : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    ewt_BottomWallThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ewt_fjord_nonvacuous

example : mci_KingRowLinked ksd_stair (![1, 1] : Site 2) :=
  ksc_kingRowLinked_of_noKingSeparation ksd_stair ksd_mem_interior_11 ksc_ksd_noKingSeparation

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationBottomWall
