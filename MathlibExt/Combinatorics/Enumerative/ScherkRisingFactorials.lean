/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.Enumerative.HsuShiueGeneralizedStirlingNumber

/-!
# Scherk's identity with rising factorials

Scherk's identity expresses a polynomial sum weighted by step-`s` rising factorials
as a sum of iterated derivatives with Hsu–Shiue coefficients.
-/

namespace MetaMathlibExt

open Polynomial

namespace sum_risingStep_mul_coeff_eq_sum_hsuShiue_derivative

private theorem expand_risingStep (s : ℝ) (S : ℕ → ℕ → ℝ) (hS : IsHsuShiueFamily S (-s) 1 0)
    (k r : ℕ) :
    ∏ j ∈ Finset.range r, ((k : ℝ) + j * s) =
      ∑ i ∈ Finset.range (r + 1), S r i * k.descFactorial i := by
  obtain ⟨_, hcol, htri, hrec⟩ := hS
  induction r with
  | zero => simp [hcol, generalizedFallingFactorial]
  | succ r ih =>
    let weight (i : ℕ) := ((i : ℝ) + r * s) * S r i * k.descFactorial i
    have hstep (i : ℕ) :
        S r i * k.descFactorial i * ((k : ℝ) + r * s) =
          S r i * k.descFactorial (i + 1) + weight i := by
      have h : (k.descFactorial i : ℝ) * k =
          k.descFactorial (i + 1) + i * (k.descFactorial i : ℝ) := by
        exact_mod_cast Nat.descFactorial_mul_self k i
      dsimp only [weight]
      linear_combination S r i * h
    -- Shift the terms that keep the same factorial order. The extra top entry vanishes.
    have shift : ∑ i ∈ Finset.range (r + 1), weight i =
        (∑ i ∈ Finset.range (r + 1), weight (i + 1)) + weight 0 := by
      rw [Finset.sum_range_succ' weight, Finset.sum_range_succ (fun i => weight (i + 1)) r]
      simp [weight, htri r (r + 1) r.lt_succ_self]
    rw [Finset.prod_range_succ, ih, Finset.sum_mul]
    simp_rw [hstep]
    rw [Finset.sum_add_distrib, shift, ← add_assoc, ← Finset.sum_add_distrib,
      Finset.sum_range_succ' (fun i => S (r + 1) i * (k.descFactorial i : ℝ))]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrec]
      simp [weight, add_mul, Nat.cast_add]
    · simp [weight, hcol, generalizedFallingFactorial, mul_comm]

end sum_risingStep_mul_coeff_eq_sum_hsuShiue_derivative

/-- **Scherk's identity with $s$-rising factorials.** Let $s$ be a real number and let $S(n, k)$
be the generalized Stirling numbers of Hsu and Shiue with parameters $(-s, 1, 0)$: a real array
with $S(0, 0) = 1$, $S(n, 0) = 0$ for $n \ge 1$, $S(n, k) = 0$ for $n < k$, and
$S(n+1, k+1) = S(n, k) + (k + 1 + ns) \, S(n, k+1)$ for all $n, k \ge 0$. Let $N$ and $r$ be
natural numbers, let $a_0, \dots, a_N$ be real numbers, and let $f(y) = \sum_{k=0}^{N} a_k y^k$,
with $i$-th derivative $f^{(i)}$. Then for every real number $x > 0$,
$$\sum_{k=0}^{N} k (k + s) \cdots (k + (r-1)s) \, a_k x^{k + rs} =
\sum_{i=0}^{r} S(r, i) \, x^{rs + i} f^{(i)}(x),$$
where the product $k (k + s) \cdots (k + (r-1)s)$ has the $r$ factors $k + js$, $0 \le j < r$,
and is $1$ when $r = 0$.

The powers of $x$ have real exponents, which is why $x > 0$ is assumed.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.1, equation (2.2). -/
public theorem sum_risingStep_mul_coeff_eq_sum_hsuShiue_derivative (s : ℝ)
    (S : ℕ → ℕ → ℝ) (hS : IsHsuShiueFamily S (-s) 1 0) (a : ℕ → ℝ) (N r : ℕ) (x : ℝ)
    (hx : 0 < x) :
    ∑ k ∈ Finset.range (N + 1),
        (∏ j ∈ Finset.range r, ((k : ℝ) + j * s)) * a k * x ^ ((k : ℝ) + r * s) =
      ∑ i ∈ Finset.range (r + 1), S r i * x ^ ((r : ℝ) * s + i) *
        (derivative^[i] (∑ k ∈ Finset.range (N + 1), C (a k) * X ^ k)).eval x := by
  simp_rw [sum_risingStep_mul_coeff_eq_sum_hsuShiue_derivative.expand_risingStep s S hS,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iterate_derivative_sum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
    eval_mul, eval_C, eval_pow, eval_X, Real.rpow_add hx, Real.rpow_natCast]
  by_cases hik : i ≤ k
  · rw [show x ^ k = x ^ i * x ^ (k - i) by rw [← pow_add, Nat.add_sub_of_le hik]]
    ring
  · simp [Nat.descFactorial_of_lt (lt_of_not_ge hik)]

end MetaMathlibExt
