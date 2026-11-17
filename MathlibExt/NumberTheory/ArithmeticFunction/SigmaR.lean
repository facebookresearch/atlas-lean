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

* `ArithmeticFunction.sigmaR`
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

/-- The complex-valued arithmetic function `σ_s(n) = ∑_{d ∣ n} d ^ s`. -/
noncomputable def sigmaR (s : ℂ) : ArithmeticFunction ℂ where
  toFun := fun n => ∑ d ∈ n.divisors, (d : ℂ) ^ s
  map_zero' := by simp

/-- The defining finite divisor-sum formula for `sigmaR`. -/
theorem sigmaR_apply {n : ℕ} {s : ℂ} :
    sigmaR s n = ∑ d ∈ n.divisors, (d : ℂ) ^ s := by
  rfl

/-- Every complex-exponent divisor sum takes the value one at one. -/
@[simp]
theorem sigmaR_apply_one (s : ℂ) : sigmaR s 1 = 1 := by
  simp [sigmaR_apply]

/-- At exponent zero, `sigmaR` counts the divisors of its input. -/
@[simp]
theorem sigmaR_zero_apply (n : ℕ) :
    sigmaR 0 n = (n.divisors.card : ℂ) := by
  simp [sigmaR_apply]

/-- At a natural exponent, `sigmaR` agrees with Mathlib's divisor-power sum after coercion to
`ℂ`. -/
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
