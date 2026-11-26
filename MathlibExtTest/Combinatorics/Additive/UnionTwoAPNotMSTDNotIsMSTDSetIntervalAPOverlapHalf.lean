/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.UnionTwoAPNotMSTDNotIsMSTDSetIntervalAPOverlapHalf
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.Combinatorics.Additive.UnionTwoAPNotMSTDNotIsMSTDSetIntervalAPOverlapHalf

open MetaMathlibExt

#check @not_isMSTDSet_intervalAP_overlap_half
#print axioms MetaMathlibExt.not_isMSTDSet_intervalAP_overlap_half

example : ¬ IsMSTDSet (realIntervalSet 3 ∪ realAPSet (1 / 2) 2 2) := by
  apply not_isMSTDSet_intervalAP_overlap_half 3 2 2 0 (1 / 2) <;> norm_num

example : ¬ IsMSTDSet (realIntervalSet 10 ∪ realAPSet (1 / 2) 2 2) := by
  apply not_isMSTDSet_intervalAP_overlap_half 10 2 2 0 (1 / 2) <;> norm_num

example : ¬ IsMSTDSet (realIntervalSet 5 ∪ realAPSet (7 / 2) 3 4) := by
  apply not_isMSTDSet_intervalAP_overlap_half 5 3 4 3 (7 / 2) <;> norm_num

example : ¬ IsMSTDSet (realIntervalSet 8 ∪ realAPSet (1 / 2) 2 3) := by
  apply not_isMSTDSet_intervalAP_overlap_half 8 2 3 0 (1 / 2) <;> norm_num

end MathlibExtTest.Combinatorics.Additive.UnionTwoAPNotMSTDNotIsMSTDSetIntervalAPOverlapHalf
