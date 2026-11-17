/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.SigmaR

/-!
# Tests for complex-exponent divisor sums
-/

@[expose] public section

open ArithmeticFunction

example (s : ℂ) : sigmaR s 0 = 0 := by
  simp

example (s : ℂ) : sigmaR s 1 = 1 := by
  simp

example (k n : ℕ) : sigmaR (k : ℂ) n = (sigma k n : ℂ) := by
  exact sigmaR_natCast_apply k n

example (n : ℕ) : sigmaR (0 : ℂ) n = (n.divisors.card : ℂ) := by
  exact sigmaR_zero_apply n

/-! ### The Dirichlet-character twist -/

example (q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : χ.sigmaR s 0 = 0 := by
  simp

example (q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : χ.sigmaR s 1 = 1 := by
  simp

-- Modulus one: the twist is the untwisted divisor sum.
example (s : ℂ) : (1 : DirichletCharacter ℂ 1).sigmaR s = sigmaR s :=
  DirichletCharacter.sigmaR_modOne _ s

-- The principal character modulo `4` kills the even divisors: `σ_{s,χ₀}(2) = 1`.
example (s : ℂ) : (1 : DirichletCharacter ℂ 4).sigmaR s 2 = 1 := by
  have h2 : (1 : DirichletCharacter ℂ 4) ((2 : ℕ) : ZMod 4) = 0 :=
    MulChar.map_nonunit _ (by decide)
  rw [DirichletCharacter.sigmaR_apply, Nat.Prime.sum_divisors Nat.prime_two, h2]
  simp

-- For `χ₀` modulo `4` and odd `n`, the twist agrees with the untwisted sum: `σ_{s,χ₀}(3) = 1 + 3^s`.
example (s : ℂ) : (1 : DirichletCharacter ℂ 4).sigmaR s 3 = sigmaR s 3 := by
  have h3 : (1 : DirichletCharacter ℂ 4) ((3 : ℕ) : ZMod 4) = 1 :=
    MulChar.one_apply (by decide)
  rw [DirichletCharacter.sigmaR_apply, sigmaR_apply, Nat.Prime.sum_divisors Nat.prime_three,
    Nat.Prime.sum_divisors Nat.prime_three, h3]
  simp
