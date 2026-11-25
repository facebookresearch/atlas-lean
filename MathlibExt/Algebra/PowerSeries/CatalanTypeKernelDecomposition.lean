/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.PowerSeries.UnifiedCatalanTypePolynomials

/-! # Decomposition of a unified Catalan-type generating function -/

namespace MetaMathlibExt

open PowerSeries

/-- **Splitting the numerator of a unified Catalan-type generating function.** Let
$j, k, m, d, n$ be natural numbers, let $a, b, c, \lambda, x, y$ be real numbers and let $A$ be
a polynomial with integer coefficients. Let $K(t)$ be the negative real power of the trinomial
$c - a x t + b (2x - 1)^d t^m$ with exponent $\lambda$ as a power series in $t$ (for $c > 0$ and
$m \ge 1$ this is the expansion of $(c - a x t + b (2x - 1)^d t^m)^{-\lambda}$ in powers of $t$),
and let $S(t) = \sum_i y^i t^i / i!$, the sum running over the natural numbers $i \ge k$ with
$j \mid i - k$ (for $j \ge 1$ this is the pseudo-Bessel function $S(j, k, yt)$ of Equation (5)).
Then the coefficient of $t^n$ in $(S(t) + A(x)\, t)\, K(t)$ equals the coefficient of $t^n$ in
$S(t) K(t)$, plus the coefficient of $t^n$ in $(1 + A(x)\, t)\, K(t)$, minus the coefficient of
$t^n$ in $K(t)$.

In the paper's notation this is
$P^{j.k;\lambda,A}_{n,m}(x, y) = P^{j.k;\lambda,0}_{n,m}(x, y) + P^{1.0;\lambda,A}_{n,m}(x) -
P^{1.0;\lambda,0}_{n,m}(x)$; the kernel is the paper's for $c > 0$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 6
(`integers-2026-A105-thm-6`). -/
public theorem coeff_catalanTypeKernel_decomposition (j k m d n : ℕ)
    (a b c lam x y : ℝ) (A : Polynomial ℤ) :
    let K : PowerSeries ℝ := trinomialNegPowSeries lam c (a * x) (b * (2 * x - 1) ^ d) m
    let S : PowerSeries ℝ :=
      PowerSeries.mk fun i ↦ if k ≤ i ∧ j ∣ i - k then y ^ i / (i.factorial : ℝ) else 0
    let At : PowerSeries ℝ := C (Polynomial.aeval x A) * X
    coeff n ((S + At) * K) = coeff n (S * K) + coeff n ((1 + At) * K) - coeff n K := by
  intro K S At
  simp only [add_mul, one_mul, map_add]
  rw [← add_assoc, add_right_comm _ (coeff n K), add_sub_cancel_right]

end MetaMathlibExt
