/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationSECorner

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSeparationSECorner`

* `cat_fjord_nonvacuous`.
* `cat_residuals_iff_noKingSeparation_of_fourThin` for `ksd_stair`: all five residual predicates
  of the chain hold there (they are equivalent to `ksc_NoKingSeparation`).
* `cat_noKingSeparation_of_fourThin` instantiated with `ksd_stair` at the seed `(1, 1)`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationSECorner

example : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    cat_CrossArcThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  cat_fjord_nonvacuous

example : kns_EscapeThickPoint ksd_stair (![1, 1] : Site 2) :=
  ((cat_residuals_iff_noKingSeparation_of_fourThin ksd_stair ksd_mem_interior_11
    ksd_stair_fourThin).2.2.2.2).mpr ksc_ksd_noKingSeparation

example : ksc_NoKingSeparation ksd_stair (![1, 1] : Site 2) :=
  cat_noKingSeparation_of_fourThin ksd_stair ksd_mem_interior_11 ksd_stair_fourThin
    cat_ksd_crossArcThick

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationSECorner
