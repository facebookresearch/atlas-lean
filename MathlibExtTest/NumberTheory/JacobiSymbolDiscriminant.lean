/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
import MathlibExt.NumberTheory.JacobiSymbolDiscriminant

open MetaMathlibExt

-- An odd positive discriminant does not require the primes to agree modulo 4.
example : jacobiSym 5 13 = jacobiSym 5 3 :=
  jacobiSym_prime_add_mul_eq (x := 2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (Int.isCoprime_iff_gcd_eq_one.mpr (by decide)) (by decide)

-- For a negative odd discriminant, the two reciprocity signs cancel.
example : jacobiSym (-7) 17 = jacobiSym (-7) 3 :=
  jacobiSym_prime_add_mul_eq (x := -2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (Int.isCoprime_iff_gcd_eq_one.mpr (by decide)) (by decide)

-- At D = 12, the primes need not agree modulo 8.
example : jacobiSym 12 17 = jacobiSym 12 5 :=
  jacobiSym_prime_add_mul_eq (x := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (Int.isCoprime_iff_gcd_eq_one.mpr (by decide)) (by decide)

-- At D = -24, the power of 2 has odd exponent.
example : jacobiSym (-24) 29 = jacobiSym (-24) 5 :=
  jacobiSym_prime_add_mul_eq (x := -1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (Int.isCoprime_iff_gcd_eq_one.mpr (by decide)) (by decide)

example : jacobiSym (-7) 3 = -1 := by norm_num
example : jacobiSym 12 5 = -1 := by norm_num
