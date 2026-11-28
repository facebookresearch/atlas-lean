/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.WilsonGlaisherCongruence

/-! # Tests for Glaisher's congruence -/

open MathlibExt.NumberTheory.WilsonFaulhaberWanted

-- The negative sign of B₁ is essential at the prime two: the error is 4, not 2.
example : padicNorm 2 ((Nat.factorial (2 - 1) : ℚ) - (2 * bernoulli (2 - 1) - 2)) =
    (2 : ℚ) ^ (-2 : ℤ) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [show (Nat.factorial (2 - 1) : ℚ) - (2 * bernoulli (2 - 1) - 2) = (2 : ℚ) ^ 2 by
    norm_num [Nat.factorial_succ, bernoulli_one]]
  rw [pow_two, padicNorm.mul, show padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ from
    padicNorm.padicNorm_p_of_prime (p := 2)]
  norm_num

-- The smallest odd prime gives error 9/2, with norm exactly 3⁻².
example : padicNorm 3 ((Nat.factorial (3 - 1) : ℚ) - (3 * bernoulli (3 - 1) - 3)) =
    (3 : ℚ) ^ (-2 : ℤ) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h2 : padicNorm 3 (2 : ℚ) = 1 := (padicNorm.nat_eq_one_iff 2).mpr (by decide)
  rw [show (Nat.factorial (3 - 1) : ℚ) - (3 * bernoulli (3 - 1) - 3) = (3 : ℚ) ^ 2 / 2 by
    norm_num [Nat.factorial_succ, bernoulli_two], padicNorm.div, h2, div_one]
  rw [pow_two, padicNorm.mul, show padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ from
    padicNorm.padicNorm_p_of_prime (p := 3)]
  norm_num

-- B₄ is negative and the error is 175/6, with norm exactly 5⁻².
example : padicNorm 5 ((Nat.factorial (5 - 1) : ℚ) - (5 * bernoulli (5 - 1) - 5)) =
    (5 : ℚ) ^ (-2 : ℤ) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h4 : bernoulli 4 = -1 / 30 :=
    (bernoulli_eq_bernoulli'_of_ne_one (by decide)).trans bernoulli'_four
  have h6 : padicNorm 5 (6 : ℚ) = 1 := (padicNorm.nat_eq_one_iff 6).mpr (by decide)
  have h7 : padicNorm 5 (7 : ℚ) = 1 := (padicNorm.nat_eq_one_iff 7).mpr (by decide)
  rw [show (Nat.factorial (5 - 1) : ℚ) - (5 * bernoulli (5 - 1) - 5) = (5 : ℚ) ^ 2 * 7 / 6 by
    norm_num [Nat.factorial_succ, h4], padicNorm.div, padicNorm.mul, h6, h7, mul_one, div_one]
  rw [pow_two, padicNorm.mul, show padicNorm 5 (5 : ℚ) = (5 : ℚ)⁻¹ from
    padicNorm.padicNorm_p_of_prime (p := 5)]
  norm_num

example : padicNorm 5 ((Nat.factorial (5 - 1) : ℚ) - (5 * bernoulli (5 - 1) - 5)) ≤
    (5 : ℚ) ^ (-2 : ℤ) :=
  wilson_mod_prime_sq_bernoulli 5 (by decide)
