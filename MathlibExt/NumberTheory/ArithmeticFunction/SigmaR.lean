/-
Copyright (c) 2026 Alex Kontorovich and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich and contributors, Adam Kiezun
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Divisor sums with a complex exponent

This file defines the complex-exponent divisor sum as a complex-valued arithmetic function.

## Main definitions

* `ArithmeticFunction.sigmaR`

## Main statements

* `ArithmeticFunction.sigmaR_apply`
* `ArithmeticFunction.sigmaR_apply_one`
* `ArithmeticFunction.sigmaR_zero_apply`
* `ArithmeticFunction.sigmaR_natCast_apply`

## References

The definition follows the convention `σ_s(n) = ∑_{d ∣ n} d ^ s`. Its Lean representation is
adapted from the Apache-2.0 licensed `ArithmeticFunction.sigmaR` declaration in
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), revision
`be5e07e04cde20c5ceabf63759bd097a9c88173f`, in `PrimeNumberTheoremAnd.IwaniecKowalskiCh1`.
-/

@[expose] public section

namespace ArithmeticFunction

/-- **Divisor-power sum with complex exponent.** For a complex number $s$, $\sigma_s$ is the
complex-valued arithmetic function with $\sigma_s(n) = \sum_{d \mid n} d^s$ for every natural
number $n \ge 1$, where $d^s$ is the complex power, and $\sigma_s(0) = 0$. -/
noncomputable def sigmaR (s : ℂ) : ArithmeticFunction ℂ where
  toFun := fun n => ∑ d ∈ n.divisors, (d : ℂ) ^ s
  map_zero' := by simp

/-- **Divisor-sum formula for the complex-exponent divisor sum.** For every natural number $n$
and complex number $s$, the divisor-power sum $\sigma_s$ with complex exponent $s$ satisfies
$\sigma_s(n) = \sum_{d \mid n} d^s$, the sum running over the positive divisors $d$ of $n$; for
$n = 0$ the sum is empty, so $\sigma_s(0) = 0$. -/
theorem sigmaR_apply {n : ℕ} {s : ℂ} :
    sigmaR s n = ∑ d ∈ n.divisors, (d : ℂ) ^ s := by
  rfl

/-- **The complex-exponent divisor sum at one.** For every complex number $s$, the divisor-power
sum $\sigma_s(n) = \sum_{d \mid n} d^s$ with complex exponent $s$ satisfies $\sigma_s(1) = 1$. -/
@[simp]
theorem sigmaR_apply_one (s : ℂ) : sigmaR s 1 = 1 := by
  simp [sigmaR_apply]

/-- **The complex-exponent divisor sum at exponent zero counts divisors.** Let
$\sigma_s(n) = \sum_{d \mid n} d^s$ be the divisor-power sum with complex exponent $s$. For
every natural number $n$, $\sigma_0(n)$ equals the number of positive divisors of $n$, with the
convention that $0$ has no divisors, so that $\sigma_0(0) = 0$. -/
@[simp]
theorem sigmaR_zero_apply (n : ℕ) :
    sigmaR 0 n = (n.divisors.card : ℂ) := by
  simp [sigmaR_apply]

/-- **Natural exponents give the classical divisor function.** For all natural numbers $k$ and
$n$, the value at $n$ of the complex-exponent divisor sum $\sum_{d \mid n} d^s$ with $s = k$
equals the natural number $\sigma_k(n) = \sum_{d \mid n} d^k$, viewed as a complex number. -/
@[simp]
theorem sigmaR_natCast_apply (k n : ℕ) :
    sigmaR (k : ℂ) n = (sigma k n : ℂ) := by
  simp [sigmaR_apply, sigma_apply, Complex.cpow_natCast]

end ArithmeticFunction
