/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Transcription.ListSortImpl

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

private def listSortExample : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := some 30 },
        { key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 2, value := some 21 }] }

/-- Small executable regression for run extension, stable forward order, and
the final temporary-storage cleanup. -/
example :
    (listSortImpl? (fun left right : Nat => decide (left < right))
      false true listSortExample).map
        (fun result =>
          (result.returnCode, result.fuelExhausted, result.state.a.backing,
            result.state.data.entries.toList)) =
      some
        (0, false, .inline,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 2, value := some 21 },
           { key := 3, value := some 30 }]) := by
  decide

/-- CPython's reverse-before/stable-sort/reverse-after pattern keeps equal-key
payloads in their original order while reversing the requested key order. -/
example :
    (listSortImpl? (fun left right : Nat => decide (left < right))
      true true listSortExample).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 3, value := some 30 },
           { key := 2, value := some 20 },
           { key := 2, value := some 21 },
           { key := 1, value := some 10 }]) := by
  decide

end CPythonListsort
