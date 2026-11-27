/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SuperFibocatalan

/-! # Boundary and sign checks for the Fibonacci and Lucas Catalan identities -/

open MathlibExt.NumberTheory.SuperFibocatalanWanted

example : (Nat.fib 0 : ℤ) * Nat.fib 2 - (Nat.fib 2 : ℤ) * Nat.fib 0 = 0 :=
  fib_mul_sub_mul 0

example : (Nat.fib 6 : ℤ) * Nat.fib 5 - (Nat.fib 8 : ℤ) * Nat.fib 3 = -2 :=
  fib_mul_sub_mul 3

example : (Nat.fib 8 : ℤ) * Nat.fib 6 - (Nat.fib 10 : ℤ) * Nat.fib 4 = 3 :=
  fib_mul_sub_mul 4

example : fiboCatalan 0 = 1 := by
  norm_num [fiboCatalan, MetaMathlibExt.fibonacciFactorial, Nat.fib]

example : 2 * fiboCatalan 1 - fiboCatalan 2 = -1 := by
  have h := fiboCatalan_identity 1
  norm_num [Nat.fib, MetaMathlibExt.fibonacciFactorial] at h
  exact h

example : 15 * fiboCatalan 2 - 2 * fiboCatalan 3 = 5 := by
  have h := fiboCatalan_identity 2
  norm_num [Nat.fib, MetaMathlibExt.fibonacciFactorial] at h
  exact h

example : fibonomial 1 2 = 0 := by simp [fibonomial]

example : fibonomial 3 1 / (Nat.fib 3 : ℚ) = 1 := by
  rw [← (fib_mul_factorialQuotient_eq_and_isInt 1 le_rfl).1]
  norm_num [MetaMathlibExt.fibonacciFactorial, Nat.fib]

example : ∃ k : ℤ, (k : ℚ) = fibonomial 7 3 / (Nat.fib 5 : ℚ) := by
  obtain ⟨h, hk⟩ := fib_mul_factorialQuotient_eq_and_isInt 3 (by decide)
  simpa only [h] using hk

open MvPolynomial

example : lucasPoly 0 * lucasPoly 2 - lucasPoly 2 * lucasPoly 0 = 0 := by
  simpa only [lucasPoly, mul_zero] using lucasPoly_mul_sub_mul 0

example : lucasPoly 2 * lucasPoly 3 - lucasPoly 4 * lucasPoly 1 = -(X 0 * X 1) := by
  calc
    _ = _ := lucasPoly_mul_sub_mul 1
    _ = _ := by simp [lucasPoly]

example : lucasPoly 4 * lucasPoly 4 - lucasPoly 6 * lucasPoly 2 = X 0 ^ 2 * X 1 ^ 2 := by
  calc
    _ = _ := lucasPoly_mul_sub_mul 2
    _ = _ := by simp [lucasPoly, pow_two, mul_comm, mul_assoc]

example : lucasFactorial 0 = 1 := by
  simp [lucasFactorial]

example :
    (lucasPoly 3 * lucasPoly 2 * lucasPoly 3 - lucasPoly 4 * lucasPoly 3 * lucasPoly 1) *
      lucasFactorial 2 = -(X 0 ^ 2 * X 1 * (X 0 ^ 2 + X 1)) := by
  have h : Finset.Icc 1 (2 : ℕ) = {1, 2} := by decide
  calc
    _ = _ := lucasCatalan_identity_mul_factorial 1
    _ = _ := by
      change (-1) ^ 1 * X 1 ^ 1 * lucasPoly 2 * lucasPoly 1 * lucasPoly 3 * lucasFactorial 2 = _
      simp [lucasFactorial, h, lucasPoly, pow_two]
      ring
