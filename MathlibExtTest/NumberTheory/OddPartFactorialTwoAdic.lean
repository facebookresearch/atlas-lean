/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OddPartFactorialTwoAdic

/-!
# Tests for normalized odd double factorials
-/

open MetaMathlibExt

-- The dyadic interval is empty when the exponent is zero.
example : oddDoubleFactorial 0 = 1 := by decide

-- The first division would already be inexact at the excluded exponent.
example : ¬ (4 : ℤ) ∣ (oddDoubleFactorial 2 : ℤ) - 1 := by decide

-- At the first admissible exponent the quotients differ but agree modulo four.
example : ((oddDoubleFactorial 3 : ℤ) - 1) / 8 = 13 ∧
    ((oddDoubleFactorial 4 : ℤ) - 1) / 16 = 126689 := by decide

example : (4 : ℤ) ∣ ((oddDoubleFactorial 3 : ℤ) - 1) / 8 -
    ((oddDoubleFactorial 4 : ℤ) - 1) / 16 :=
  (oddDoubleFactorial_normalized_congr 3 (by decide)).2.2
