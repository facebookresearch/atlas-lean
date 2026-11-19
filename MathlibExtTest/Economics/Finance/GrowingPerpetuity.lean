/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.GrowingPerpetuity
import Mathlib.Tactic.NormNum

/-!
# Tests for the growing perpetuity

`C₁ = 3`, `r = 1/2`, `g = 1/4` (ratio `5/6`) is worth `12`; a level perpetuity of `10` at
`r = 1/10` is worth `100`; with `g = -1` only the first payment counts and the value is
`5/2`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.GrowingPerpetuity

open MathlibExt.Economics.Finance

-- Test section: concrete instances of the Gordon growth formula.

example : MathlibExt.Economics.Finance.growingPerpetuity 3 (1 / 2) (1 / 4) = 12 := by
  have h := MathlibExt.Economics.Finance.growingPerpetuity_eq (3 : ℝ) (1 / 2) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

example : MathlibExt.Economics.Finance.growingPerpetuity 10 (1 / 10) 0 = 100 := by
  have h := MathlibExt.Economics.Finance.growingPerpetuity_eq (10 : ℝ) (1 / 10) 0
    (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

example : MathlibExt.Economics.Finance.growingPerpetuity 5 1 (-1) = 5 / 2 := by
  have h := MathlibExt.Economics.Finance.growingPerpetuity_eq (5 : ℝ) 1 (-1)
    (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

end MathlibExtTest.Economics.Finance.GrowingPerpetuity
