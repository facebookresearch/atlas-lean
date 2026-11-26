/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrinomialEvenGenerating
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The constant row has value one at every weight.
example (z s : ℂ) (hs : s ^ 2 = z) : ∑ k ∈ Finset.range (0 + 1),
    (trinomialCoefficient 0 (2 * k) : ℂ) * z ^ k = 1 := by
  rw [sum_trinomialCoefficient_even 0 z s hs]
  norm_num

-- The square root may be zero, including for nonconstant rows.
example (n : ℕ) : ∑ k ∈ Finset.range (n + 1),
    (trinomialCoefficient n (2 * k) : ℂ) * (0 : ℂ) ^ k = 1 := by
  rw [sum_trinomialCoefficient_even n 0 0 (by simp)]
  norm_num

-- Row two at weight one counts the entries 1, 3, 1, using the negative root.
example : ∑ k ∈ Finset.range (2 + 1),
    (trinomialCoefficient 2 (2 * k) : ℂ) * (1 : ℂ) ^ k = 5 := by
  rw [sum_trinomialCoefficient_even 2 1 (-1) (by norm_num)]
  norm_num
