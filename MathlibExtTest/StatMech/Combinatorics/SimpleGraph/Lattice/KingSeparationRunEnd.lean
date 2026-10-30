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

* `gtp_fjord_nonvacuous`; `gtp_kingRowLinked_of_fourThin` instantiated with `kda_stairDR`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationRunEnd

example : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    gtp_RunEndReconnect sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  gtp_fjord_nonvacuous

example : mci_KingRowLinked kda_stairDR (![3, 1] : Site 2) :=
  gtp_kingRowLinked_of_fourThin kda_stairDR kda_mem_interior_31 kda_stairDR_fourThin
    gtp_kda_runEndReconnect

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationRunEnd
