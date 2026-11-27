/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.EntrySnapshotPermutation

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

private def wrongPayloadKeyedInput : ListSortInput Nat Nat :=
  ListSortInput.keyed #[(1, 10), (2, 20)]

private def wrongPayloadTaggedSlice : SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[{ key := { value := 1, origin := 0 }, value := some 10 },
        { key := { value := 2, origin := 1 }, value := some 99 }] }

/-- Anti-vacuity regression: the key projections are exactly equal, while the
second keyed payload changes from `20` to `99`; that payload-only corruption
does not satisfy the whole-entry snapshot invariant. -/
theorem entrySnapshotPermutation_rejects_wrong_keyed_payload :
    wrongPayloadTaggedSlice.entries.map SortSliceEntry.key =
        (tagSortSliceOccurrences wrongPayloadKeyedInput.slice).entries.map
          SortSliceEntry.key ∧
      wrongPayloadTaggedSlice.entries.map SortSliceEntry.value =
        #[some 10, some 99] ∧
      (tagSortSliceOccurrences wrongPayloadKeyedInput.slice).entries.map
          SortSliceEntry.value = #[some 10, some 20] ∧
      wrongPayloadTaggedSlice.entries.map SortSliceEntry.value ≠
        (tagSortSliceOccurrences wrongPayloadKeyedInput.slice).entries.map
          SortSliceEntry.value ∧
      ¬EntrySnapshotPermutation wrongPayloadKeyedInput.slice
        wrongPayloadTaggedSlice := by
  simp [EntrySnapshotPermutation, wrongPayloadKeyedInput,
    wrongPayloadTaggedSlice, ListSortInput.keyed, tagSortSliceOccurrences]

end CPythonListsort
