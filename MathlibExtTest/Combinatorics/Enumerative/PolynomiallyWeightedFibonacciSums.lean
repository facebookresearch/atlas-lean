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
