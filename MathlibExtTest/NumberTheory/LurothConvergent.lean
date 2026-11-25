/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LurothConvergent
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The initial convergent of 1 attains the upper bound.
example :
    let d := lurothDigitSeq 1
    1 - (lurothConvergent d 0 : ℝ) = 1 / (((d 0 : ℝ) - 1) * lurothDenominator d 0) := by
  norm_num [lurothConvergent, lurothDenominator, lurothDigitSeq, lurothDigit]

-- At 4/9 the first two digits differ, and the second error lies strictly inside the bound.
example :
    let d := lurothDigitSeq (4 / 9)
    lurothConvergent d 1 = 5 / 12 ∧
      (4 / 9 : ℝ) - lurothConvergent d 1 < 1 / (((d 1 : ℝ) - 1) * lurothDenominator d 1) := by
  have h₀ : ⌊(9 / 4 : ℝ)⌋₊ = 2 := (Nat.floor_eq_iff (by norm_num)).2 (by norm_num)
  have h₁ : ⌊(3 / 2 : ℝ)⌋₊ = 1 := (Nat.floor_eq_iff (by norm_num)).2 (by norm_num)
  norm_num [lurothConvergent, lurothDenominator, Finset.sum_range_succ, Finset.prod_range_succ,
    lurothDigitSeq, lurothMap, lurothDigit, h₀, h₁]
