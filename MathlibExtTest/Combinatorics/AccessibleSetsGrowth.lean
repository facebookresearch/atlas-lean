/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AccessibleSetsGrowth

/-! # Tests for eventual growth and two-accessibility -/

namespace MetaMathlibExt.not_two_accessible_of_growth

-- The first gap ratio is two. The growth factor four is attained from the second gap onwards.
private def gaps : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * 4 ^ n

example : ¬ IsRAccessible 2 (Set.range gaps) := by
  refine not_two_accessible_of_growth _ gaps ?_ rfl (by decide) 1 (by norm_num) 2 (by decide) ?_
  · apply strictMono_nat_of_lt_succ
    intro n
    cases n with
    | zero => decide
    | succ n =>
      simp only [gaps, pow_succ]
      have : 0 < 4 ^ n := pow_pos (by decide) _
      omega
  · intro n hn
    cases n with
    | zero => omega
    | succ n =>
      simp [gaps, pow_succ]
      linarith

end MetaMathlibExt.not_two_accessible_of_growth
