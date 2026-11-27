/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PolynomiallyWeightedFibonacciSums
import Mathlib.Tactic.NormNum

/-! # Tests for polynomially weighted Fibonacci sums -/

open MetaMathlibExt Polynomial

-- A constant weight recovers the generating polynomial itself, including at x = 0.
example (N : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (N + 1), (Nat.fib k : ℂ) * x ^ k =
      (∑ k ∈ Finset.range (N + 1), C (Nat.fib k : ℂ) * X ^ k).eval x := by
  simpa using sum_poly_mul_fib_pow_eq_sum_stirlingSecond_derivative (fun _ => 1) 0 N x

-- A cubic weight on the degree-two polynomial includes a derivative above its degree.
example (x : ℂ) :
    ∑ i ∈ Finset.range 4, (Nat.stirlingSecond 3 i : ℂ) * x ^ i *
      (derivative^[i] (X + X ^ 2 : ℂ[X])).eval x = x + 8 * x ^ 2 := by
  have h := sum_poly_mul_fib_pow_eq_sum_stirlingSecond_derivative
    (fun r => if r = 3 then 1 else 0) 3 2 x
  norm_num [ite_mul, Finset.sum_range_succ, Nat.fib] at h ⊢
  exact h.symm

-- The constant binomial weight recovers the unweighted identity with a complex scale.
example (a : ℂ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, a * N.choose k * Nat.fib k = a * Nat.fib (2 * N) := by
  simpa using (sum_poly_mul_choose_mul_fib (fun _ => a) N 0).1

-- At degree five in row two, falling factorials above order two vanish.
example :
    ∑ k ∈ Finset.Icc (1 : ℕ) 2,
        (∑ j ∈ Finset.range 6, (if j = 5 then (1 : ℂ) else 0) * (k : ℂ) ^ j) *
          (2 : ℕ).choose k * Nat.fib k = 34 := by
  rw [(sum_poly_mul_choose_mul_fib (fun j => if j = 5 then 1 else 0) 2 5).1]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.descFactorial, Nat.fib]

-- The quartic formula needs no assumptions on the row index.
example (A : ℕ → ℂ) :
    ∑ k ∈ Finset.Icc (1 : ℕ) 0,
        (∑ j ∈ Finset.range 5, A j * (k : ℂ) ^ j) * (0 : ℕ).choose k * Nat.fib k = 0 := by
  rw [(sum_poly_mul_choose_mul_fib A 0 0).2]
  norm_num [Nat.choose, Nat.fib]

example (A : ℕ → ℂ) :
    ∑ k ∈ Finset.Icc (1 : ℕ) 1,
        (∑ j ∈ Finset.range 5, A j * (k : ℂ) ^ j) * (1 : ℕ).choose k * Nat.fib k =
      A 0 + A 1 + A 2 + A 3 + A 4 := by
  rw [(sum_poly_mul_choose_mul_fib A 1 0).2]
  norm_num [Nat.choose, Nat.fib, add_assoc]

-- In row four, all five terms of the quartic formula contribute.
example :
    ∑ k ∈ Finset.Icc (1 : ℕ) 4,
        (∑ j ∈ Finset.range 5, (k : ℂ) ^ j) * (4 : ℕ).choose k * Nat.fib k = 2197 := by
  have h := (sum_poly_mul_choose_mul_fib (fun _ => 1) 4 0).2
  simp only [one_mul] at h
  rw [h]
  norm_num [Nat.choose, Nat.fib]
