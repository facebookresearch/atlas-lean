/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparation

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparation`

* `ksc_NoKingSeparation` holds for the staircase walks and fails for the fjord.
* `ksc_kingInteriorConnected_of_noKingSeparation` and `ksc_noKingSeparation_iff_kingStepReachable`
  instantiated with `ksd_stair` at its interior seed `(1, 1)`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparation

example : ksc_NoKingSeparation ksd_stair (![1, 1] : Site 2) ∧
    ksc_NoKingSeparation kda_stairDR (![3, 1] : Site 2) ∧
    ¬ ksc_NoKingSeparation sdc_fjord (![5, 1] : Site 2) :=
  ⟨ksc_ksd_noKingSeparation, ksc_kda_noKingSeparation, ksc_fjord_noKingSeparation_false⟩

/-- The interior of the staircase walk is king-connected. -/
example : mci_KingInteriorConnected ksd_stair :=
  ksc_kingInteriorConnected_of_noKingSeparation ksd_stair ksd_mem_interior_11
    ksc_ksd_noKingSeparation

example : ∀ z : jil_offSupportInterior ksd_stair,
    (mci_interiorKingGraph ksd_stair).Reachable z ⟨_, ksd_mem_interior_11⟩ :=
  (ksc_noKingSeparation_iff_kingStepReachable ksd_stair ksd_mem_interior_11).mp
    ksc_ksd_noKingSeparation

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparation
