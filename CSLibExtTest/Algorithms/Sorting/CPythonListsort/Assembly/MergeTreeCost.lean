/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.MergeTreeCost

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Exact branch-and-cost regression -/

/-- Kernel-checked regression for the reviewed adaptive-minrun counterexample
to literal final-tree equality.  The scan has already paid 213 and leaves
open-subtree lengths `[148, 36, 32, 32, 8]`.  Paper top-pair completion totals
476, whereas CPython's strict third-last branch lowers it to 472, giving
complete costs 689 and 685. -/
private theorem forceCollapse_rotation_cost_regression :
    topPairCompletionCost [148, 36, 32, 32, 8] = 476 ∧
      CPythonForceCollapseCost [148, 36, 32, 32, 8] 472 ∧
      213 + 476 = 689 ∧
      213 + 472 = 685 := by
  refine ⟨by norm_num [topPairCompletionCost], ?_, by norm_num, by norm_num⟩
  apply CPythonForceCollapseCost.mergeTop [148, 36] 32 32 8 432
  · norm_num
  apply CPythonForceCollapseCost.mergeThirdLast [148] 36 32 40 364
  · norm_num
  apply CPythonForceCollapseCost.mergeTop [] 148 68 40 256
  · norm_num
  exact CPythonForceCollapseCost.pair 148 108

end CPythonListsort
