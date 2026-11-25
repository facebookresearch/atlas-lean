/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AACarmichaelGcd

open MetaMathlibExt

-- The two shifted differences are 390 and 462, with one of the original values negative.
example : Int.gcd ((-10 : ℤ) - (-400)) (62 - (-400)) = 6 := by
  apply int_gcd_sub_eq_of_eq_mul_mul_add (-400) 6 10 21 13 11 5 7 <;> decide

-- A zero common factor allows the two original values to coincide at any integer.
example (a : ℤ) : Int.gcd (a - a) (a - a) = 0 := by
  apply int_gcd_sub_eq_of_eq_mul_mul_add a 0 10 21 1 1 5 7
  all_goals first | decide | simp

-- At a prime equal to the shift, the divisibility condition reads zero divides zero.
example : IsAACarmichael 3 3 := isAACarmichael_of_prime 3 Nat.prime_three
