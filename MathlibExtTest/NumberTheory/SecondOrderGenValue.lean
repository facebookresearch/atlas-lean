/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SecondOrderGenValue
meta import MathlibExt.NumberTheory.SecondOrderGenValue
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

/-! ### Values of the generating function -/

example : secondOrderGenValue 1 3 1 (1 / 3) = 3 := by
  norm_num [secondOrderGenValue]

example : secondOrderGenValue 1 0 1 (1 / 3) = 6 / 5 := by
  norm_num [secondOrderGenValue]

example (a b p : ℤ) : secondOrderGenValue a b p 0 = a :=
  secondOrderGenValue_zero a b p

-- For `p = 0` the denominator vanishes at `x = 1`, and the value is the junk value `0`.
example (a b : ℤ) : secondOrderGenValue a b 0 1 = 0 := by
  norm_num [secondOrderGenValue]

#guard secondOrderGenValue 1 3 1 (1 / 3) = 3
#guard secondOrderGenValue 1 3 1 2 = -1
#guard secondOrderGenValue 2 5 0 1 = 0

/-! ### The integrality criterion -/

-- `D = 3 ^ 2 - 1 * 3 - 1 = 5` and `3⁻¹ ≡ 2 (mod 5)`: `A(1/3)` is an integer as `3 ≡ -2 (mod 5)`.
example : ∃ z : ℤ, secondOrderGenValue 1 3 1 ((1 : ℤ) / (3 : ℤ)) = z := by
  rw [secondOrderGenValue_integer_iff 1 3 1 one_ne_zero 1 3 (by norm_num) (by norm_num)]
  intro t ht
  norm_num [Int.ModEq] at ht ⊢
  omega

-- With `b = 0` the congruence `0 ≡ -2 (mod 5)` fails, and indeed `A(1/3) = 6/5`.
example : ¬ ∃ z : ℤ, secondOrderGenValue 1 0 1 ((1 : ℤ) / (3 : ℤ)) = z := by
  rw [secondOrderGenValue_integer_iff 1 0 1 one_ne_zero 1 3 (by norm_num) (by norm_num)]
  intro h
  have h2 := h 2 (by decide)
  revert h2
  decide

-- A negative modulus: at `x = 2/1`, `D = 1 - 2 - 4 = -5`, and `A(2) = -1`.
example : ∃ z : ℤ, secondOrderGenValue 1 3 1 ((2 : ℤ) / (1 : ℤ)) = z := by
  rw [secondOrderGenValue_integer_iff 1 3 1 one_ne_zero 2 1 (by norm_num) (by norm_num)]
  intro t ht
  norm_num [Int.ModEq] at ht ⊢
  omega

-- When `D = 1`, as at `x = 1/2` for `p = 1`, every value is an integer.
example (a b : ℤ) : ∃ z : ℤ, secondOrderGenValue a b 1 ((1 : ℤ) / (2 : ℤ)) = z := by
  rw [secondOrderGenValue_integer_iff a b 1 one_ne_zero 1 2 (by norm_num) (by norm_num)]
  intro t _
  norm_num [Int.modEq_one]

end MetaMathlibExt
