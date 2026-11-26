/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.GibonacciPolynomialRatioTelescoping
import MathlibExt.NumberTheory.GibonacciPolynomialInverseRatio

/-!
# Telescoping powered gibonacci polynomial ratios at odd multiples

The sum of successive differences of powered Fibonacci or Lucas polynomial ratios
at odd multiples of `k` is the initial ratio power minus its limit.
-/

namespace MetaMathlibExt

open Polynomial

/-- The Fibonacci polynomials `f_n(x)`. -/
local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1

/-- The Lucas polynomials `l_n(x)`. -/
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

/-- **Telescoping sum of powers of gibonacci polynomial ratios.** Let $f_n$ and $l_n$ denote the
Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$, $l_1 = x$ and
$g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, l\}$, evaluated at a real number $x > 0$, and let
$\alpha = (x + \sqrt{x^2 + 4})/2$. Then for $g \in \{f, l\}$, every positive integer $k$ and all
natural numbers $r$ and $\lambda$,
$$\sum_{n \ge 0} \left(\frac{g_{(2n+1)k+r}^\lambda}{g_{(2n+1)k}^\lambda} -
\frac{g_{(2n+3)k+r}^\lambda}{g_{(2n+3)k}^\lambda}\right)
= \frac{g_{k+r}^\lambda}{g_k^\lambda} - \alpha^{r\lambda}.$$

Source: Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Lemma 2.1. -/
public theorem tsum_gibonacciPoly_pow_ratio_telescope {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k : ℕ} (hk : 0 < k) (r lam : ℕ) :
    ∑' n : ℕ, (aeval x (g ((2 * n + 1) * k + r)) ^ lam / aeval x (g ((2 * n + 1) * k)) ^ lam -
        aeval x (g ((2 * n + 3) * k + r)) ^ lam / aeval x (g ((2 * n + 3) * k)) ^ lam) =
      aeval x (g (k + r)) ^ lam / aeval x (g k) ^ lam - ((x + √(x ^ 2 + 4)) / 2) ^ (r * lam) := by
  rcases Nat.eq_zero_or_pos lam with rfl | hlam
  · simp
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · -- With zero shift, the forward and inverse ratios coincide.
    simpa using tsum_gibonacciPoly_pow_inv_ratio_telescope hx hg hk 0 lam
  have h := hasSum_gibonacciPoly_pow_ratio_telescoping g hg hx (p := 1) (t := 1)
    hk hr (by decide) hlam (by decide)
  have hnext (n : ℕ) : 2 * 1 * (n + 1) + 1 = 2 * n + 3 := by omega
  have hprev (n : ℕ) : 2 * n + 3 - 2 * 1 = 2 * n + 1 := by omega
  simpa only [hnext, hprev, one_mul, div_pow, Nat.mul_comm lam r] using h.tsum_eq

end MetaMathlibExt
