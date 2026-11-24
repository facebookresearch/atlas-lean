/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Fib.Basic

/-!
# Polynomially weighted Fibonacci sums

Expanding a power of the index in falling factorials expresses a polynomially weighted
Fibonacci sum in terms of derivatives of the finite Fibonacci generating polynomial.
-/

namespace MetaMathlibExt

open Polynomial

/-- **Polynomially weighted Fibonacci sums via derivatives.** Let $F_n$ denote the Fibonacci
numbers and $S(r, i)$ the Stirling numbers of the second kind. Let $t$ and $N$ be natural numbers,
let $A_0, \dots, A_t$ be complex numbers, let $h(y) = \sum_{r=0}^{t} A_r y^r$, and let $P$ be the
polynomial $P(y) = \sum_{j=0}^{N} F_j y^j$, with $i$-th derivative $P^{(i)}$. Then for every
$x \in \mathbb{C}$,
$$\sum_{k=0}^{N} h(k) F_k x^k = \sum_{r=0}^{t} A_r \sum_{i=0}^{r} S(r, i) \, x^i P^{(i)}(x).$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.4. -/
public theorem sum_poly_mul_fib_pow_eq_sum_stirlingSecond_derivative (A : ℕ → ℂ)
    (t N : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (N + 1),
        (∑ r ∈ Finset.range (t + 1), A r * (k : ℂ) ^ r) * (Nat.fib k : ℂ) * x ^ k =
      ∑ r ∈ Finset.range (t + 1), A r * ∑ i ∈ Finset.range (r + 1),
        (Nat.stirlingSecond r i : ℂ) * x ^ i *
          (derivative^[i] (∑ j ∈ Finset.range (N + 1), C (Nat.fib j : ℂ) * X ^ j)).eval x := by
  have hpow (k r : ℕ) : (k : ℂ) ^ r = ∑ i ∈ Finset.range (r + 1),
      (Nat.stirlingSecond r i : ℂ) * k.descFactorial i := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial k r
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp only [iterate_derivative_sum, eval_finsetSum, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul, eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range (r + 1))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hpow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ≤ k
  · rw [show x ^ k = x ^ i * x ^ (k - i) by rw [← pow_add, Nat.add_sub_of_le hi]]
    ring
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hi)]

end MetaMathlibExt
