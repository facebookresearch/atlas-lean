/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Equivalence.MinrunResults

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-- At exponent 33 the selected 32-bit transcription mask no longer agrees with the
ideal full-width mask: the second actual target is 63 rather than 64.  This is
kernel-checked executable evidence that the width restriction on exact
equivalence is substantive. -/
private theorem minrun_cIntMask_truncation_regression :
    let listSize : PySSize := BitVec.ofNat 64 (2 ^ 39 - 2 ^ 32)
    (minrunInit listSize).mr_e.toNat = 33 ∧
      (minrunInit listSize).mr_mask.toNat = 2 ^ 32 - 1 ∧
      (minrunNextN 2 (minrunInit listSize)).outputs = [63, 63] ∧
      (minrunSpecTrace 2 listSize.toNat 33 0).outputs = [63, 64] := by
  decide

end CPythonListsort
