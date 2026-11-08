/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticDerivative
import Mathlib.Tactic.NormNum.Prime

namespace MetaMathlibExtTest

open MetaMathlibExt

example : arithmeticDerivative 0 = 0 := arithmeticDerivative_zero

example : arithmeticDerivative 1 = 0 := arithmeticDerivative_one

example : arithmeticDerivative 7 = 1 := arithmeticDerivative_prime (by norm_num)

/-- `D(12) = D(2 · 2 · 3) = 16`, via the Leibniz rule. -/
example : arithmeticDerivative 12 = 16 := by
  rw [show (12 : ℕ) = 2 * 2 * 3 by norm_num, arithmeticDerivative_mul, arithmeticDerivative_mul,
    arithmeticDerivative_prime Nat.prime_two, arithmeticDerivative_prime Nat.prime_three]

/-- `D(p²) = 2p`. -/
example {p : ℕ} (hp : p.Prime) : arithmeticDerivative (p * p) = 2 * p := by
  rw [arithmeticDerivative_mul, arithmeticDerivative_prime hp]
  omega

/-- The defining formula unfolds on a concrete value: `D(12) = ν₂ · 6 + ν₃ · 4`. -/
example : arithmeticDerivative 12 = ∑ p ∈ ({2, 3} : Finset ℕ), (12 : ℕ).factorization p * (12 / p) :=
  arithmeticDerivative_eq_sum_of_subset (by
    intro p hp
    have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [h12, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three] at hp
    simpa using hp)

end MetaMathlibExtTest
