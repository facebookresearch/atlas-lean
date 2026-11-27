/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.MergeGetmemStorageValid

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Regression: why live input is essential -/

/-- A concrete impossible-at-a-merge-boundary state: `alloced` remains eight,
as it can after `merge_freemem`, while the payload is empty and released. -/
def fabricatedStaleReleasedMergeState : MergeState Unit Unit :=
  { min_gallop := MIN_GALLOP
    listlen := 0
    basekeys := 0
    data := { entries := #[] }
    a :=
      { cells := #[]
        backing := .released
        hasValues := false }
    alloced := 8
    pending := #[]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- The raw transcription will reuse the stale capacity in the fabricated
released state: the representation invariant holds, the signed reuse test for
four cells succeeds, and the result remains released.  Only `TempStorage.Live`
separates this invalid merge-boundary state from the public safety theorem. -/
theorem fabricatedStaleReleasedMergeState_reuses :
    let state := fabricatedStaleReleasedMergeState
    let need : PySSize := 4
    TempStorageInv state.a state.alloced ∧
      ¬ state.a.Live ∧
      need.sle state.alloced = true ∧
      (mergeGetmem state need).outcome = .reused ∧
      (mergeGetmem state need).state = state ∧
      (mergeGetmem state need).state.a.backing = .released := by
  simp [fabricatedStaleReleasedMergeState, TempStorageInv, TempStorage.Live,
    mergeGetmem]

end CPythonListsort
