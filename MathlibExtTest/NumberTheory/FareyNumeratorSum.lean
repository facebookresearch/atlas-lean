/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FareyNumeratorSum
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.FareyNumeratorWanted

-- At the smallest admissible pair, the numerator-1 endpoint contributes.
example :
    (∑ h ∈ Finset.Icc 1 1, (fareyNumeratorCount 2 h : ℚ)) = 2 ∧
    (1 + (2 : ℚ) * ∑ h ∈ Finset.Icc 1 1, (Nat.totient h : ℚ) / h -
      ∑ h ∈ Finset.Icc 1 1, (Nat.totient h : ℚ) -
      ∑ h ∈ Finset.Icc 1 1, ∑ d ∈ h.divisors,
        (ArithmeticFunction.moebius d : ℚ) * (((2 % d : ℕ) : ℚ) / d)) = 2 := by
  constructor
  · decide +kernel
  · norm_num [Nat.divisors_one, ArithmeticFunction.moebius_apply_one]

-- There are five unit fractions and two fractions with numerator 2 (2/3 and 2/5).
-- The divisor 2 also gives a nonzero remainder in the formula.
example :
    (∑ h ∈ Finset.Icc 1 2, (fareyNumeratorCount 5 h : ℚ)) = 7 ∧
    (1 + (5 : ℚ) * ∑ h ∈ Finset.Icc 1 2, (Nat.totient h : ℚ) / h -
      ∑ h ∈ Finset.Icc 1 2, (Nat.totient h : ℚ) -
      ∑ h ∈ Finset.Icc 1 2, ∑ d ∈ h.divisors,
        (ArithmeticFunction.moebius d : ℚ) * (((5 % d : ℕ) : ℚ) / d)) = 7 := by
  constructor
  · decide +kernel
  · have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide +kernel
    have hdiv : (2 : ℕ).divisors = {1, 2} := by decide +kernel
    norm_num [hIcc, hdiv, Finset.sum_insert, Nat.divisors_one, Nat.totient_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
