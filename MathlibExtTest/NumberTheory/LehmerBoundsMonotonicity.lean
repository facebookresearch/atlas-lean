/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.LehmerBoundsMonotonicity

open MetaMathlibExt

-- At length two, raising the prefix from 2 to 3 excludes tails below 3.
example : lehmerLower [3] 2 ≤ lehmerLower [2] 2 ∧ lehmerUpper [3] 2 ≤ lehmerUpper [2] 2 := by
  refine lehmerLower_upper_antitone 2 [2] [3] (by decide) (by simp) (by simp) ?_ ?_
  · intro x hx
    simpa only [List.mem_singleton.mp hx] using (le_rfl : (2 : ℝ) ≤ 2)
  · exact .cons (by norm_num) .nil

-- Full-length singleton prefixes have only the empty completion.
example : lehmerLower [4] 1 ≤ lehmerLower [2] 1 ∧ lehmerUpper [4] 1 ≤ lehmerUpper [2] 1 := by
  refine lehmerLower_upper_antitone 1 [2] [4] (by decide) (by simp) (by simp) ?_ ?_
  · intro x hx
    simpa only [List.mem_singleton.mp hx] using (le_rfl : (2 : ℝ) ≤ 2)
  · exact .cons (by norm_num) .nil
