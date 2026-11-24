/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.ScanRemainder

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-- Concrete keyed-input pin: occurrence tagging keeps the payload `42`
paired with key `7` while attaching absolute origin zero. -/
private theorem listSortInput_keyed_occurrence_payload_regression :
    let input := ListSortInput.keyed (#[(7, 42)] : Array (Nat × Nat))
    input.withOccurrenceKeys.hasKeyfunc = true ∧
      input.withOccurrenceKeys.slice.entries =
        #[{ key := { value := 7, origin := 0 }, value := some 42 }] := by
  norm_num [ListSortInput.withOccurrenceKeys, ListSortInput.keyed,
    tagSortSliceOccurrences]

end CPythonListsort
