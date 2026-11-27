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
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.RationallyWeightedBinomialSums

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

/-- **Polynomially weighted binomial Fibonacci sums.** Let $F_n$ denote the Fibonacci numbers,
$S(j, i)$ the Stirling numbers of the second kind and $(N)_i = N(N-1)\cdots(N-i+1)$ the falling
factorial. Let $A_0, A_1, A_2, \dots$ be complex numbers and $N$, $t$ natural numbers, and put
$h(y) = \sum_{j=0}^{t} A_j y^j$. Then

$$\sum_{k=1}^{N} h(k) \binom{N}{k} F_k =
\sum_{j=0}^{t} A_j \sum_{i=0}^{j} S(j, i)\, (N)_i\, F_{2N-i}.$$

Moreover,
$\sum_{k=1}^{N} (A_0 + A_1 k + A_2 k^2 + A_3 k^3 + A_4 k^4) \binom{N}{k} F_k$ equals
$A_0 F_{2N} + (A_1 + A_2 + A_3 + A_4) \binom{N}{1} F_{2N-1} +
2(A_2 + 3A_3 + 7A_4) \binom{N}{2} F_{2N-2} + 6(A_3 + 6A_4) \binom{N}{3} F_{2N-3} +
24 A_4 \binom{N}{4} F_{2N-4}$.

The source's hypotheses $N, t > 0$ and $t \le N/2$ are not needed and are dropped.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.7. -/
public theorem sum_poly_mul_choose_mul_fib (A : ℕ → ℂ) (N t : ℕ) :
    (∑ k ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.range (t + 1), A j * (k : ℂ) ^ j) * N.choose k * Nat.fib k =
      ∑ j ∈ Finset.range (t + 1), A j * ∑ i ∈ Finset.range (j + 1),
        (Nat.stirlingSecond j i : ℂ) * N.descFactorial i * Nat.fib (2 * N - i)) ∧
    ∑ k ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.range 5, A j * (k : ℂ) ^ j) * N.choose k * Nat.fib k =
      A 0 * Nat.fib (2 * N) + (A 1 + A 2 + A 3 + A 4) * N.choose 1 * Nat.fib (2 * N - 1) +
        2 * (A 2 + 3 * A 3 + 7 * A 4) * N.choose 2 * Nat.fib (2 * N - 2) +
        6 * (A 3 + 6 * A 4) * N.choose 3 * Nat.fib (2 * N - 3) +
        24 * A 4 * N.choose 4 * Nat.fib (2 * N - 4) := by
  have moment (j : ℕ) :
      ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ j * N.choose k * Nat.fib k =
        ∑ i ∈ Finset.range (j + 1),
          (Nat.stirlingSecond j i : ℂ) * N.descFactorial i * Nat.fib (2 * N - i) := by
    have h := sum_pow_mul_choose_mul_fib N j
    -- The term at zero vanishes even for the constant monomial.
    rw [Finset.range_eq_Ico (N + 1), Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)] at h
    simp only [Nat.fib_zero, mul_zero, zero_add, Nat.succ_eq_add_one,
      Finset.Ico_add_one_right_eq_Icc] at h
    exact_mod_cast h
  have sum_poly (d : ℕ) :
      ∑ k ∈ Finset.Icc 1 N,
          (∑ j ∈ Finset.range (d + 1), A j * (k : ℂ) ^ j) * N.choose k * Nat.fib k =
        ∑ j ∈ Finset.range (d + 1), A j * ∑ i ∈ Finset.range (j + 1),
          (Nat.stirlingSecond j i : ℂ) * N.descFactorial i * Nat.fib (2 * N - i) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simpa only [Finset.mul_sum, mul_assoc] using congrArg (A j * ·) (moment j)
  refine ⟨sum_poly t, ?_⟩
  rw [sum_poly 4]
  -- The falling-factorial rewrite also holds for orders above `N`.
  simp only [Finset.sum_range_succ, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  norm_num [Nat.stirlingSecond, Nat.factorial]
  ring

end MetaMathlibExt
