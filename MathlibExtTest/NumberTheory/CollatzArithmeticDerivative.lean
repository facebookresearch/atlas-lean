/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CollatzArithmeticDerivative
import Mathlib.Tactic.NormNum.Prime

open MetaMathlibExt

example : collatzAccelerated 0 = 0 ∧ collatzAccelerated 3 = 5 ∧ collatzAccelerated 6 = 3 :=
  ⟨rfl, rfl, rfl⟩

-- The compatible semiprimes `71 · 1609` and `349 · 491` give a positive solution of
-- `D(C(n)) = C(D(n))`: both sides are `840`, and the solution is odd.
example : arithmeticDerivative (collatzAccelerated (71 * 1609)) =
      collatzAccelerated (arithmeticDerivative (71 * 1609)) ∧ Odd (71 * 1609) := by
  have h : arithmeticDerivative (collatzAccelerated (71 * 1609)) =
      collatzAccelerated (arithmeticDerivative (71 * 1609)) := by
    rw [show collatzAccelerated (71 * 1609) = 349 * 491 from rfl, arithmeticDerivative_mul,
      arithmeticDerivative_mul, arithmeticDerivative_prime (by norm_num : Nat.Prime 349),
      arithmeticDerivative_prime (by norm_num : Nat.Prime 491),
      arithmeticDerivative_prime (by norm_num : Nat.Prime 71),
      arithmeticDerivative_prime (by norm_num : Nat.Prime 1609)]
    rfl
  exact ⟨h, odd_of_arithmeticDerivative_collatz_comm _ (by norm_num) h⟩

-- The positivity hypothesis is needed: `n = 0` solves the equation but is even.
example : arithmeticDerivative (collatzAccelerated 0) =
      collatzAccelerated (arithmeticDerivative 0) ∧ ¬ Odd 0 :=
  ⟨by simp [collatzAccelerated, arithmeticDerivative_zero], by decide⟩

-- No positive even number solves the equation.
example (m : ℕ) (hm : 0 < m) :
    arithmeticDerivative (collatzAccelerated (2 * m)) ≠
      collatzAccelerated (arithmeticDerivative (2 * m)) := fun h =>
  Nat.not_odd_iff_even.mpr (even_two_mul m)
    (odd_of_arithmeticDerivative_collatz_comm _ (by omega) h)

-- The two semiprimes in the example realize opposite residue orders.
example : (71 * 1609 % 3 = 2 ∧ 349 * 491 % 3 = 2) ∧
    (71 % 3 = 2 ∧ 1609 % 3 = 1) ∧ (349 % 3 = 1 ∧ 491 % 3 = 2) := by
  obtain ⟨hpq, hrs, h₁, h₂⟩ := isCompatibleSemiprimePair_71_1609.mod_three
  exact ⟨⟨hpq, hrs⟩, h₁.resolve_left (by decide), h₂.resolve_right (by decide)⟩

-- Both equations hold, but the first product is divisible by three.
example : 2 * (11 + 43) = 3 + 105 ∧ 2 * (11 * 43) = 3 * (3 * 105) + 1 ∧
    ¬ IsCompatibleSemiprimePair 3 105 11 43 := by
  refine ⟨rfl, rfl, fun h => ?_⟩
  exact (by decide : 3 * 105 % 3 ≠ 2) h.mod_three.1

example : 71 * 1609 % 4 = 3 ∧ 71 % 4 = 3 ∧ 1609 % 4 = 1 := by
  obtain ⟨hprod, hres⟩ := isCompatibleSemiprimePair_71_1609.mod_four
  exact ⟨hprod, hres.resolve_left (by decide)⟩

-- Both equations hold, but 62 is composite and the first product is 1 modulo 4.
example : 2 * (19 + 62) = 5 + 157 ∧ 2 * (19 * 62) = 3 * (5 * 157) + 1 ∧
    ¬ IsCompatibleSemiprimePair 5 157 19 62 := by
  refine ⟨rfl, rfl, fun h => ?_⟩
  exact (by decide : 5 * 157 % 4 ≠ 3) h.mod_four.1

-- The prime gap bound for the solution `1609 · 71`: `1609 - 71 = 1538` and
-- `2 √(30 · 1609² + 2) - 10 · 1609 ≈ 1536.2`, so the bound is nearly sharp here.
example : 2 * Real.sqrt (30 * (1609 : ℝ) ^ 2 + 2) - 10 * 1609 ≤ (1609 : ℝ) - 71 := by
  have h : arithmeticDerivative (collatzAccelerated (1609 * 71)) =
      collatzAccelerated (arithmeticDerivative (1609 * 71)) := by
    rw [show collatzAccelerated (1609 * 71) = 349 * 491 from rfl, arithmeticDerivative_mul,
      arithmeticDerivative_mul, arithmeticDerivative_prime (by norm_num : Nat.Prime 349),
      arithmeticDerivative_prime (by norm_num : Nat.Prime 491),
      arithmeticDerivative_prime (by norm_num : Nat.Prime 1609),
      arithmeticDerivative_prime (by norm_num : Nat.Prime 71)]
    rfl
  exact_mod_cast prime_gap_bound_of_arithmeticDerivative_collatz_comm 1609 71
    (by norm_num) (by norm_num) (by norm_num) h

-- The bound rules out the twin primes `5` and `3`: `2 √752 - 50 > 2`, since `26² < 752`.
example : arithmeticDerivative (collatzAccelerated (5 * 3)) ≠
    collatzAccelerated (arithmeticDerivative (5 * 3)) := by
  intro h
  have hb := prime_gap_bound_of_arithmeticDerivative_collatz_comm 5 3
    (by norm_num) (by norm_num) (by norm_num) h
  have h26 : (26 : ℝ) < Real.sqrt (30 * ((5 : ℕ) : ℝ) ^ 2 + 2) :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  push_cast at hb h26
  linarith
