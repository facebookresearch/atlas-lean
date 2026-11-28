/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.TrinomialOddGenerating

open MetaMathlibExt

-- The constant row has no odd powers.
example (z s : ℂ) (hs : s ^ 2 = z) (hs0 : s ≠ 0) : ∑ k ∈ Finset.range (0 + 1),
    (trinomialCoefficient 0 (2 * k + 1) : ℂ) * z ^ k = 0 := by
  rw [sum_trinomialCoefficient_odd 0 z s hs hs0]
  simp

-- Row two has odd coefficients 2 and 2. The weight 4 gives 2 + 2 * 4.
example : ∑ k ∈ Finset.range (2 + 1),
    (trinomialCoefficient 2 (2 * k + 1) : ℂ) * (4 : ℂ) ^ k = 10 := by
  rw [sum_trinomialCoefficient_odd 2 4 2 (by norm_num) (by norm_num)]
  norm_num

-- Choosing the opposite square root gives the same value.
example : ∑ k ∈ Finset.range (2 + 1),
    (trinomialCoefficient 2 (2 * k + 1) : ℂ) * (4 : ℂ) ^ k = 10 := by
  rw [sum_trinomialCoefficient_odd 2 4 (-2) (by norm_num) (by norm_num)]
  norm_num
