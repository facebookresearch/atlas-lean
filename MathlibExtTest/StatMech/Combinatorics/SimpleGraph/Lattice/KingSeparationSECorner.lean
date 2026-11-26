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
* `kns_ksd_escapeThickPoint`: the first residual predicate holds for `ksd_stair`.
* `ksc_ksd_noKingSeparation`: `ksd_stair` has no king separation from `(1, 1)`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationSECorner

example : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    cat_CrossArcThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  cat_fjord_nonvacuous

example : kns_EscapeThickPoint ksd_stair (![1, 1] : Site 2) := kns_ksd_escapeThickPoint

example : ksc_NoKingSeparation ksd_stair (![1, 1] : Site 2) := ksc_ksd_noKingSeparation

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSeparationSECorner
