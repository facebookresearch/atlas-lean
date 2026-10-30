/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationThickPoint

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationThickPoint`

* `kns_fjord_nonvacuous`: the fjord has a king separation and a thick point.
* `kns_thickPoint_iff_not_fourThin` on the fjord.
* `kns_noKingSeparation_of_fourThin` instantiated with the 4-thin staircase `ksd_stair`, whose
  residual predicate `kns_EscapeThickPoint` holds (`kns_ksd_escapeThickPoint`). Stage B notes that
  this residual is equivalent to the conclusion for 4-thin walks.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationThickPoint

example : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    kns_EscapeThickPoint sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  kns_fjord_nonvacuous

example : kns_ThickPoint sdc_fjord :=
  (kns_thickPoint_iff_not_fourThin sdc_fjord).mpr mci_fjord_not_fourThin

example : ksc_NoKingSeparation ksd_stair (![1, 1] : Site 2) :=
  kns_noKingSeparation_of_fourThin ksd_stair ksd_mem_interior_11 ksd_stair_fourThin
    kns_ksd_escapeThickPoint

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationThickPoint
