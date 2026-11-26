/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationSWCorner

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationSWCorner`

* `etp_fjord_nonvacuous`; `etp_EscapeWallThick` holds for the staircase walks.
* `ksc_kda_noKingSeparation`: the staircase `kda_stairDR` has no king separation.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationSWCorner

example : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    etp_EscapeWallThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  etp_fjord_nonvacuous

example : ksc_NoKingSeparation kda_stairDR (![3, 1] : Site 2) := ksc_kda_noKingSeparation

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationSWCorner
