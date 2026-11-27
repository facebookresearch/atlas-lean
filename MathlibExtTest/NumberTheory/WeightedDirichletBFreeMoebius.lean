/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.WeightedDirichletBFreeMoebius

/-! # Tests for the B-free indicator convolved with Möbius -/

open MetaMathlibExt ArithmeticFunction
open scoped ArithmeticFunction.Moebius Classical

-- At one, there are no primes in the product.
example : (bFreeIndicator (fun _ => 2) * μ) 1 = 1 := by
  rw [bFreeIndicator_mul_moebius_apply (fun _ _ => by decide) (n := 1) le_rfl]
  simp

-- An odd exponent fails the divisibility test.
example : (bFreeIndicator (fun _ => 2) * μ) 2 = 0 := by
  rw [bFreeIndicator_mul_moebius_apply (fun _ _ => by decide) (n := 2) (by decide), ite_eq_right]
  intro h
  have h₂ := h 2
  rw [Nat.prime_two.factorization_self] at h₂
  exact (by decide : ¬ (2 : ℕ) ∣ 1) h₂

-- The varying threshold at 2 is three, so the root of 2 ^ 3 is prime.
example : (bFreeIndicator (fun p => if p = 2 then 3 else 2) * μ) (2 ^ 3) = -1 := by
  rw [bFreeIndicator_mul_moebius_apply (fun p _ => by split <;> decide) (by decide),
    Nat.prime_two.factorization_pow, ite_eq_left]
  · rw [Finsupp.prod_single_index (by simp)]
    simpa using moebius_apply_prime Nat.prime_two
  · intro p
    by_cases hp : p = 2
    · simp [hp]
    · simp [Ne.symm hp]

-- Exact division need not give a squarefree root: 2 ^ 4 has root 2 ^ 2.
example : (bFreeIndicator (fun _ => 2) * μ) (2 ^ 4) = 0 := by
  rw [bFreeIndicator_mul_moebius_apply (fun _ _ => by decide) (by decide),
    Nat.prime_two.factorization_pow, ite_eq_left]
  · rw [Finsupp.prod_single_index (by simp)]
    change μ (2 ^ 2) = 0
    rw [moebius_apply_prime_pow Nat.prime_two (by decide : 2 ≠ 0)]
    decide
  · intro p
    by_cases hp : p = 2
    · simp [hp]
    · simp [Ne.symm hp]
