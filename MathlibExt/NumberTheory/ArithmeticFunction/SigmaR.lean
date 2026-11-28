/-
Copyright (c) 2026 Alex Kontorovich and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich and contributors, Adam Kiezun
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Divisor sums with a complex exponent

This file defines the complex-exponent divisor sum as a complex-valued arithmetic function, and
its twist by a Dirichlet character.

## Main definitions

* `ArithmeticFunction.sigmaR`: the complex-exponent divisor sum.
* `ArithmeticFunction.sigmaPow`: the divisor sum in a semiring with a power operation.
* `DirichletCharacter.sigmaR`: the twisted divisor sum `σ_{s,χ}(n) = ∑_{d ∣ n} χ d * d ^ s`

## Main statements

* `ArithmeticFunction.sigmaR_apply`
* `ArithmeticFunction.sigmaR_apply_one`
* `ArithmeticFunction.sigmaR_zero_apply`
* `ArithmeticFunction.sigmaR_natCast_apply`
* `DirichletCharacter.sigmaR_modOne`: the twist by the character modulo `1` is the untwisted sum

## References

The definition follows the convention `σ_s(n) = ∑_{d ∣ n} d ^ s`. Its Lean representation is
adapted from the Apache-2.0 licensed `ArithmeticFunction.sigmaR` declaration in
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), revision
`be5e07e04cde20c5ceabf63759bd097a9c88173f`, in `PrimeNumberTheoremAnd.IwaniecKowalskiCh1`.
-/

@[expose] public section

namespace ArithmeticFunction

/-- **Divisor-power sum in a semiring.** Let `R` be a semiring with a power operation
`R → R → R`. For `s : R`, this arithmetic function has value `∑ d ∈ n.divisors, (d : R) ^ s`
at `n`. At `n = 0` the sum is empty. -/
noncomputable def sigmaPow {R : Type*} [Semiring R] [HPow R R R] (s : R) :
    ArithmeticFunction R where
  toFun := fun n => ∑ d ∈ n.divisors, (d : R) ^ s
  map_zero' := by simp

/-- **Divisor-sum formula for `sigmaPow`.** The sum runs over the positive divisors of `n`,
with an empty sum when `n = 0`. -/
theorem sigmaPow_apply {R : Type*} [Semiring R] [HPow R R R] {n : ℕ} {s : R} :
    sigmaPow s n = ∑ d ∈ n.divisors, (d : R) ^ s :=
  rfl

/-- **Divisor-power sum with complex exponent.** For a complex number $s$, $\sigma_s$ is the
complex-valued arithmetic function with $\sigma_s(n) = \sum_{d \mid n} d^s$ for every natural
number $n \ge 1$, where $d^s$ is the complex power, and $\sigma_s(0) = 0$. -/
noncomputable def sigmaR (s : ℂ) : ArithmeticFunction ℂ := sigmaPow s

@[inherit_doc]
scoped[ArithmeticFunction] notation "σᴿ" => ArithmeticFunction.sigmaR

/-- **Divisor-sum formula for the complex-exponent divisor sum.** For every natural number $n$
and complex number $s$, the divisor-power sum $\sigma_s$ with complex exponent $s$ satisfies
$\sigma_s(n) = \sum_{d \mid n} d^s$, the sum running over the positive divisors $d$ of $n$; for
$n = 0$ the sum is empty, so $\sigma_s(0) = 0$. -/
theorem sigmaR_apply {n : ℕ} {s : ℂ} :
    sigmaR s n = ∑ d ∈ n.divisors, (d : ℂ) ^ s :=
  sigmaPow_apply

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
    sigmaR (0 : ℂ) n = (n.divisors.card : ℂ) := by
  simp [sigmaR_apply]

/-- **Natural exponents give the classical divisor function.** For all natural numbers $k$ and
$n$, the value at $n$ of the complex-exponent divisor sum $\sum_{d \mid n} d^s$ with $s = k$
equals the natural number $\sigma_k(n) = \sum_{d \mid n} d^k$, viewed as a complex number. -/
@[simp]
theorem sigmaR_natCast_apply (k n : ℕ) :
    sigmaR (k : ℂ) n = (sigma k n : ℂ) := by
  simp [sigmaR_apply, sigma_apply, Complex.cpow_natCast]

end ArithmeticFunction

namespace DirichletCharacter

variable {q : ℕ}

/-- The divisor sum twisted by a Dirichlet character, `σ_{s,χ}(n) = ∑_{d ∣ n} χ d * d ^ s`. -/
noncomputable def sigmaR (χ : DirichletCharacter ℂ q) (s : ℂ) : ArithmeticFunction ℂ where
  toFun n := ∑ d ∈ n.divisors, χ d * (d : ℂ) ^ s
  map_zero' := by simp

/-- The defining finite divisor-sum formula for `DirichletCharacter.sigmaR`. -/
theorem sigmaR_apply (χ : DirichletCharacter ℂ q) {s : ℂ} {n : ℕ} :
    χ.sigmaR s n = ∑ d ∈ n.divisors, χ d * (d : ℂ) ^ s :=
  rfl

/-- Every twisted divisor sum takes the value one at one. -/
@[simp]
theorem sigmaR_apply_one (χ : DirichletCharacter ℂ q) (s : ℂ) : χ.sigmaR s 1 = 1 := by
  simp [sigmaR_apply]

/-- Twisting by the (trivial) Dirichlet character modulo `1` does nothing. -/
theorem sigmaR_modOne (χ : DirichletCharacter ℂ 1) (s : ℂ) :
    χ.sigmaR s = ArithmeticFunction.sigmaR s := by
  ext n
  simp only [sigmaR_apply, ArithmeticFunction.sigmaR_apply]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [Subsingleton.elim (d : ZMod 1) 1, map_one, one_mul]

end DirichletCharacter
