/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.GallopCorrectness

/-! # Equality-bias regressions for the two gallops -/

namespace CPythonListsort

private def gallopDuplicateRegressionSlice : SortSlice Nat PUnit :=
  { entries := #[
      { key := 1, value := none },
      { key := 2, value := none },
      { key := 2, value := none },
      { key := 3, value := none }] }

private def gallopDuplicateRegressionState : MergeState Nat PUnit :=
  { min_gallop := 7
    listlen := 4
    basekeys := 0
    data := gallopDuplicateRegressionSlice
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

-- On `[1, 2, 2, 3]`, left galloping for `2` returns the first equal key.
example :
    gallopLeft? gallopDuplicateRegressionState gallopDuplicateRegressionSlice
      0 2 4 2 = some { index := 1, fuelExhausted := false } := by
  decide

-- Right galloping for `2` returns after the last equal key.
example :
    gallopRight? gallopDuplicateRegressionState gallopDuplicateRegressionSlice
      0 2 4 2 = some { index := 3, fuelExhausted := false } := by
  decide

end CPythonListsort
