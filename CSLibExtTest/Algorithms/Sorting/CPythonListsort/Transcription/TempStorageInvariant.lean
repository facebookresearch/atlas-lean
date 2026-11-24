/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Transcription.TempStorageInvariant

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-- A deliberately impossible inline keyed state used to pin the invariant. -/
def impossibleInlineKeyed255 : TempStorage Unit Unit :=
  { cells := Array.replicate 255 none
    backing := .inline
    hasValues := true }

/-- Inline keyed capacity 255 would require 510 physical slots, not 256. -/
theorem impossibleInlineKeyed255_not_inv :
    ¬ TempStorageInv impossibleInlineKeyed255 (255 : PySSize) := by
  simp [TempStorageInv, impossibleInlineKeyed255, TempStorage.multiplier,
    MERGESTATE_TEMP_SIZE]

end CPythonListsort
