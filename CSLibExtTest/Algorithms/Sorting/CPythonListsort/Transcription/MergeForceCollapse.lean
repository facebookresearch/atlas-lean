/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Transcription.MergeForceCollapse

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

private def forceCollapseTieExampleState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data := { entries := #[] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 1 },
        { base := 1, len := 1, power := some 2 },
        { base := 2, len := 1, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- The neighboring-length test is strict: a tie keeps `n = size - 2` and
therefore chooses the top pair rather than the lower pair. -/
example : forceCollapseIndex? forceCollapseTieExampleState = some 1 := by
  decide

end CPythonListsort
