/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationRunEnd

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationRunEnd`

* `gtp_fjord_nonvacuous`; the staircase `kda_stairDR` is king row-linked from `(3, 1)`
  via `ksc_kingRowLinked_of_noKingSeparation` and `ksc_kda_noKingSeparation`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationRunEnd

example : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    gtp_RunEndReconnect sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  gtp_fjord_nonvacuous

example : mci_KingRowLinked kda_stairDR (![3, 1] : Site 2) :=
  ksc_kingRowLinked_of_noKingSeparation kda_stairDR kda_mem_interior_31 ksc_kda_noKingSeparation

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationRunEnd
