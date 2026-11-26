/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.UnionTwoAPNotMSTDNotIsMSTDSetIntervalAPOverlapLargeDiff
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.Combinatorics.Additive.UnionTwoAPNotMSTDNotIsMSTDSetIntervalAPOverlapLargeDiff

open MetaMathlibExt

example : ¬ IsMSTDSet (realIntervalSet 3 ∪ realAPSet (1 / 2) 2 3) := by
  apply not_isMSTDSet_intervalAP_overlap_large_diff 3 2 3 (1 / 2)
    (by decide) (by decide) (by decide) _ (by norm_num) (by norm_num)
  rintro ⟨k, hk⟩
  have heq : 2 * k = 1 := by
    exact_mod_cast (show 2 * (k : ℝ) = 1 by rw [hk]; norm_num)
  omega

example (m d : ℕ) (hm : 2 ≤ m) (hd : 3 ≤ d) :
    ¬ IsMSTDSet (realIntervalSet 3 ∪ realAPSet (1 / 3) m (d : ℝ)) := by
  apply not_isMSTDSet_intervalAP_overlap_large_diff 3 m d (1 / 3)
    (by decide) hm hd _ (by norm_num) (by norm_num)
  rintro ⟨k, hk⟩
  have heq : 3 * k = 1 := by
    exact_mod_cast (show 3 * (k : ℝ) = 1 by rw [hk]; norm_num)
  omega

#check @MetaMathlibExt.not_isMSTDSet_intervalAP_overlap_large_diff
#print axioms MetaMathlibExt.not_isMSTDSet_intervalAP_overlap_large_diff

end MathlibExtTest.Combinatorics.Additive.UnionTwoAPNotMSTDNotIsMSTDSetIntervalAPOverlapLargeDiff
