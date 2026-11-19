/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.QuantityEquation

import Mathlib.Tactic

/-!
# Tests for the quantity equation

`M = 100, P = 2, Y = 150` gives `V = 3` and `M * V = 300 = P * Y`;
`M = 50, P = 4, Y = 25` gives `V = 2` and recovers `P = 4`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.QuantityEquation

open MathlibExt.Economics.Macro.QuantityEquation

example : quantityVelocity 100 2 150 = 3 := by
  unfold quantityVelocity
  norm_num

example : (100 : ℝ) * quantityVelocity 100 2 150 = 300 := by
  have h := quantityEquation 100 2 150 (by norm_num)
  norm_num at h
  exact h

example : quantityVelocity 50 4 25 = 2 := by
  unfold quantityVelocity
  norm_num

example : (50 : ℝ) * quantityVelocity 50 4 25 / 25 = 4 := by
  have h := priceLevel_from_quantity 50 4 25 (by norm_num) (by norm_num)
  exact h.symm

end MathlibExtTest.Economics.Macro.QuantityEquation
