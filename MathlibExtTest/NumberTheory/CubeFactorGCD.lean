/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CubeFactorGCD

/-! # Tests for the gcds of the factors of `x ^ 3 ± 1` -/

open MetaMathlibExt

-- Each linear factor can vanish, in which case the quadratic factor equals three.
example : Int.gcd (1 - 1) (1 ^ 2 + 1 + 1) = 3 :=
  (gcd_sub_one_sq_add_add_one 1).1.trans (by decide)

example : Int.gcd (-1 + 1) ((-1) ^ 2 - (-1) + 1) = 3 :=
  (gcd_sub_one_sq_add_add_one (-1)).2.trans (by decide)

-- At a negative input the two gcds can differ even when both linear factors are nonzero.
example : Int.gcd (-4 - 1) ((-4) ^ 2 + (-4) + 1) = 1 ∧
    Int.gcd (-4 + 1) ((-4) ^ 2 - (-4) + 1) = 3 := by
  rw [(gcd_sub_one_sq_add_add_one (-4)).1, (gcd_sub_one_sq_add_add_one (-4)).2]
  decide
