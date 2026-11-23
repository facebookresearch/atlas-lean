/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial

/-!
# More sums involving gibonacci polynomial squares, revisited (statements)

Statements from Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023.

The Fibonacci polynomials `f_n(x)` (`f_0 = 0`, `f_1 = 1`) and Lucas polynomials `l_n(x)`
(`l_0 = 2`, `l_1 = x`), both with `g_{n+2} = x g_{n+1} + g_n`, are the existing
`generalizedFibonacciPolynomial` sequences over `ℤ[X]`, evaluated at a real `x` with
`Polynomial.aeval`; `Δ = √(x² + 4)`, `α = (x + Δ)/2`, `β = (x - Δ)/2`.

The paper takes `x` to be an arbitrary integer, but every statement rests on
`g_{m+r}/g_m → α^r`, which needs `x > 0`: at `x = -1`, `f_n(-1) = (-1)^{n+1} F_n` and the
Lemma 2.1 sum with `k = r = λ = 1` equals `(√5 - 1)/2`, not `f_2/f_1 - α = -(1 + √5)/2`. The
statements below take a real `x > 0`. Infinite sums start at `n = 1` in the paper and at `n = 0`
here (index shifted by one).
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

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
public theorem_wanted tsum_gibonacciPoly_pow_ratio_telescope {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k : ℕ} (hk : 0 < k) (r lam : ℕ) :
    ∑' n : ℕ, (aeval x (g ((2 * n + 1) * k + r)) ^ lam / aeval x (g ((2 * n + 1) * k)) ^ lam -
        aeval x (g ((2 * n + 3) * k + r)) ^ lam / aeval x (g ((2 * n + 3) * k)) ^ lam) =
      aeval x (g (k + r)) ^ lam / aeval x (g k) ^ lam - ((x + √(x ^ 2 + 4)) / 2) ^ (r * lam)

/-- **Telescoping sum of powers of inverse gibonacci polynomial ratios.** Let $f_n$ and $l_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$, $l_1 = x$
and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, l\}$, evaluated at a real number $x > 0$, and
let $\beta = (x - \sqrt{x^2 + 4})/2$. Then for $g \in \{f, l\}$, every positive integer $k$ and
all natural numbers $r$ and $\lambda$,
$$\sum_{n \ge 0} \left(\frac{g_{(2n+1)k}^\lambda}{g_{(2n+1)k+r}^\lambda} -
\frac{g_{(2n+3)k}^\lambda}{g_{(2n+3)k+r}^\lambda}\right)
= \frac{g_k^\lambda}{g_{k+r}^\lambda} - (-\beta)^{r\lambda}.$$

Source: Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Lemma 2.2. -/
public theorem_wanted tsum_gibonacciPoly_pow_inv_ratio_telescope {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k : ℕ} (hk : 0 < k) (r lam : ℕ) :
    ∑' n : ℕ, (aeval x (g ((2 * n + 1) * k)) ^ lam / aeval x (g ((2 * n + 1) * k + r)) ^ lam -
        aeval x (g ((2 * n + 3) * k)) ^ lam / aeval x (g ((2 * n + 3) * k + r)) ^ lam) =
      aeval x (g k) ^ lam / aeval x (g (k + r)) ^ lam - (-((x - √(x ^ 2 + 4)) / 2)) ^ (r * lam)

/-- **Gibonacci polynomial square sums at even multiples of the index.** Let $f_n$ and $l_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$, $l_1 = x$
and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, l\}$, evaluated at a real number $x > 0$, and
let $\alpha = (x + \sqrt{x^2 + 4})/2$. Let $g$ be $f$ with $(\mu, \nu) = (1, -1)$, or $l$ with
$(\mu, \nu) = (x^2 + 4, 1)$. Then for every positive integer $k$ and every natural number $r$,
$$\sum_{n \ge 1} \frac{(-1)^{k+1} \mu \nu f_r f_{2k}}{g_{2nk}^2 + (-1)^k \mu \nu f_k^2}
= \frac{g_{k+r}}{g_k} - \alpha^r.$$

The extracted statement of this theorem prints the numerator with $(-1)^k$ in place of
$(-1)^{k+1}$, which negates the left side and makes the identity false (for $x = 1$, $g = f$ and
$k = r = 1$ that left side is $(\sqrt{5} - 1)/2$ while the right side is $(1 - \sqrt{5})/2$); the
paper's proof and its corollaries use the sign stated here.

Source: Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Theorem 3.1. -/
public theorem_wanted tsum_fib_mul_div_gibonacciPoly_sq_add {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} {μ ν : ℝ}
    (hg : (g = 𝔣 ∧ μ = 1 ∧ ν = -1) ∨ (g = 𝔩 ∧ μ = x ^ 2 + 4 ∧ ν = 1)) {k : ℕ} (hk : 0 < k)
    (r : ℕ) :
    ∑' n : ℕ, (-1) ^ (k + 1) * μ * ν * aeval x (𝔣 r) * aeval x (𝔣 (2 * k)) /
        (aeval x (g (2 * (n + 1) * k)) ^ 2 + (-1) ^ k * μ * ν * aeval x (𝔣 k) ^ 2) =
      aeval x (g (k + r)) / aeval x (g k) - ((x + √(x ^ 2 + 4)) / 2) ^ r

/-- **Gibonacci polynomial square sums at shifted even multiples of the index.** Let $f_n$ and
$l_n$ denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$,
$l_1 = x$ and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, l\}$, evaluated at a real number
$x > 0$, and let $\beta = (x - \sqrt{x^2 + 4})/2$. Let $g$ be $f$ with $(\mu, \nu) = (1, -1)$, or
$l$ with $(\mu, \nu) = (x^2 + 4, 1)$. Then for every positive integer $k$ and every natural
number $r$,
$$\sum_{n \ge 1} \frac{(-1)^k \mu \nu f_r f_{2k}}{g_{2nk+r}^2 + (-1)^{r+k} \mu \nu f_k^2}
= \frac{g_k}{g_{k+r}} - (-\beta)^r.$$

Source: Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Theorem 3.2. -/
public theorem_wanted tsum_fib_mul_div_gibonacciPoly_shift_sq_add {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} {μ ν : ℝ}
    (hg : (g = 𝔣 ∧ μ = 1 ∧ ν = -1) ∨ (g = 𝔩 ∧ μ = x ^ 2 + 4 ∧ ν = 1)) {k : ℕ} (hk : 0 < k)
    (r : ℕ) :
    ∑' n : ℕ, (-1) ^ k * μ * ν * aeval x (𝔣 r) * aeval x (𝔣 (2 * k)) /
        (aeval x (g (2 * (n + 1) * k + r)) ^ 2 + (-1) ^ (r + k) * μ * ν * aeval x (𝔣 k) ^ 2) =
      aeval x (g k) / aeval x (g (k + r)) - (-((x - √(x ^ 2 + 4)) / 2)) ^ r

end

end MetaMathlibExt
