/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RamanujanKFunction
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

open MetaMathlibExt

example : ramanujanK 0 = 0 := ramanujanK_zero

-- The square of a nonreal point of the disk can lie on the negative real axis.
example :
    let X := ramanujanK (Complex.I / 2)
    let Y := ramanujanK (-1 / 4)
    (1 + Y) * X ^ 2 + 2 * Y * X = Y * (1 - Y) := by
  have h := ramanujanK_sq_relation (Complex.I / 2) (by norm_num [norm_div])
  rw [show (Complex.I / 2) ^ 2 = -1 / 4 by norm_num [div_pow, Complex.I_sq]] at h
  dsimp only
  linear_combination h
