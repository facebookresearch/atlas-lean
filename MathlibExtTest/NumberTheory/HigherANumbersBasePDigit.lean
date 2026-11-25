/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HigherANumbersBasePDigit

open MetaMathlibExt

-- The base-`5` digits of `2/3` after the radix point start `3, 1`, as in the source's example.
example : basePDigit 5 (2 / 3) (-1) = 3 ∧ basePDigit 5 (2 / 3) (-2) = 1 ∧
    basePDigit 5 (2 / 3) 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [basePDigit, zpow_neg]

-- For `p = 2` only `d = 1` occurs; the digits of `1` after the radix point are `0`.
example : basePDigit 2 (1 : ℚ) (-2) = 0 := by
  norm_num [basePDigit, zpow_neg]

-- The digits of `3/4` in base `5` are constant after the radix point.
example : basePDigit 5 ((3 : ℚ) / 4) (-3) = basePDigit 5 ((3 : ℚ) / 4) (-2) := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact basePDigit_div_periodic_one 5 4 (by decide) 3 (by decide) 2 (by decide)

-- The digits of `5/2` in base `3` are constant after the radix point.
example : basePDigit 3 ((5 : ℚ) / 2) (-2) = basePDigit 3 ((5 : ℚ) / 2) (-1) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact basePDigit_div_periodic_one 3 2 (by decide) 5 (by decide) 1 (by decide)

-- The digits of `7` in base `2` are constant after the radix point.
example : basePDigit 2 ((7 : ℚ) / 1) (-4) = basePDigit 2 ((7 : ℚ) / 1) (-3) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact basePDigit_div_periodic_one 2 1 (by decide) 7 (by decide) 3 (by decide)
