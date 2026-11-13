/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.MergeLoInvariant
import Code.Correctness.MergeHiInvariant

/-!
# Direction-independent merge target

The forward and backward physical merge algorithms are specified by the same
left-biased whole-entry `stableEntryMerge`.  This module exports that
definitional consistency fact as a named theorem for downstream composition.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- `merge_lo` and `merge_hi` definitionally compute the same mathematical
whole-entry target when presented with the same post-trimming call. -/
theorem mergeLoTargetEntries_eq_mergeHiTargetEntries
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) :
    mergeLoTargetEntries lt call = mergeHiTargetEntries lt call := by
  rfl

end CPythonListsort
