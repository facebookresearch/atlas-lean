/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite sums involving powers of gibonacci polynomials

Statements from Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024.

The Fibonacci polynomials `f_n(x)` (`f_0 = 0`, `f_1 = 1`) and Lucas polynomials `ℓ_n(x)`
(`ℓ_0 = 2`, `ℓ_1 = x`), both with `g_{n+2} = x g_{n+1} + g_n`, are the existing
`generalizedFibonacciPolynomial` sequences over `ℤ[X]`; `Δ² = x² + 4`. Real-variable statements
evaluate them with `Polynomial.aeval`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
public import MathlibExt.NumberTheory.LucasSequence

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- The Fibonacci polynomials `f_n(x)`. -/
local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1

/-- The Lucas polynomials `ℓ_n(x)`. -/
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

/-- The paper's lower summation limit `L`: `(k + 1)/2` for odd `k`, `k/2 + 1` for even `k`. -/
local notation "𝔏[" k "]" => ite (Odd k) ((k + 1) / 2) (k / 2 + 1)

/-- The paper's lower summation limit `M`: `(k + 1)/2` for odd `k`, `k/2` for even `k`. -/
local notation "𝔐[" k "]" => ite (Odd k) ((k + 1) / 2) (k / 2)

/-- The paper's index `s`: `2r - 1` for odd `k`, `2r` for even `k`. -/
local notation "𝔰[" k ", " r "]" => ite (Odd k) (2 * r - 1) (2 * r)

/-- The paper's index `t`: `2r` for odd `k`, `2r - 1` for even `k`. -/
local notation "𝔱[" k ", " r "]" => ite (Odd k) (2 * r) (2 * r - 1)

/-- **Catalan-type identities for Fibonacci and Lucas polynomials.** Let $f_i$ and $\ell_i$ be
the Fibonacci and Lucas polynomials in $\mathbb{Z}[x]$, defined by $f_0 = 0$, $f_1 = 1$,
$\ell_0 = 2$, $\ell_1 = x$ and $g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. For all natural
numbers $k \le n$,
$$
f_{n+k} f_{n-k} - f_n^2 = (-1)^{n+k+1} f_k^2
\quad\text{and}\quad
\ell_{n+k} \ell_{n-k} - \ell_n^2 = (-1)^{n+k} (x^2 + 4) f_k^2
$$
in $\mathbb{Z}[x]$.

The source quotes this lemma from Koshy.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.1 (`fq-2024-linzhou02172024-lem-2.1`). -/
public theorem_wanted gibonacciPoly_mul_sub_sq {n k : ℕ} (hk : k ≤ n) :
    𝔣 (n + k) * 𝔣 (n - k) - 𝔣 n ^ 2 = (-1) ^ (n + k + 1) * 𝔣 k ^ 2 ∧
      𝔩 (n + k) * 𝔩 (n - k) - 𝔩 n ^ 2 = (-1) ^ (n + k) * (X ^ 2 + 4) * 𝔣 k ^ 2

/-- **Telescoping inverse-power series of gibonacci polynomials at odd indices, odd shift.**
Let $x > 0$ be real, and let $g_n$ denote either the Fibonacci polynomials, given by $g_0 = 0$ and
$g_1 = 1$, or the Lucas polynomials, given by $g_0 = 2$ and $g_1 = x$, both satisfying
$g_{n+2} = x g_{n+1} + g_n$ and evaluated at $x$. Let $k$ be an odd natural number and
$\lambda$ a positive integer. Then
$$\sum_{n=0}^{\infty} \left(\frac{1}{g_{2n+1}^{\lambda}} - \frac{1}{g_{2n+1+2k}^{\lambda}}\right) =
\sum_{r=1}^{k} \frac{1}{g_{2r-1}^{\lambda}}.$$

The source quotes this lemma from Koshy as the sum over $n \ge (k + 1)/2$ of
$1/g_{2n-k}^{\lambda} - 1/g_{2n+k}^{\lambda}$; here the summation index is shifted to start at $0$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.2 (`fq-2024-linzhou02172024-lem-2.2`). -/
public theorem_wanted tsum_inv_pow_gibonacciPoly_sub_odd {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Odd k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 1)) ^ lam - 1 / aeval x (g (2 * n + 1 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r - 1)) ^ lam

/-- **Telescoping inverse-power series of gibonacci polynomials at even indices, even shift.**
Let $x > 0$ be real, and let $g_n$ denote either the Fibonacci polynomials, given by $g_0 = 0$ and
$g_1 = 1$, or the Lucas polynomials, given by $g_0 = 2$ and $g_1 = x$, both satisfying
$g_{n+2} = x g_{n+1} + g_n$ and evaluated at $x$. Let $k$ be an even natural number and
$\lambda$ a positive integer. Then
$$\sum_{n=0}^{\infty} \left(\frac{1}{g_{2n+2}^{\lambda}} - \frac{1}{g_{2n+2+2k}^{\lambda}}\right) =
\sum_{r=1}^{k} \frac{1}{g_{2r}^{\lambda}}.$$

The source quotes this lemma from Koshy as the sum over $n \ge k/2 + 1$ of
$1/g_{2n-k}^{\lambda} - 1/g_{2n+k}^{\lambda}$; here the summation index is shifted to start at $0$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.3 (`fq-2024-linzhou02172024-lem-2.3`). -/
public theorem_wanted tsum_inv_pow_gibonacciPoly_sub_even {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Even k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 2)) ^ lam - 1 / aeval x (g (2 * n + 2 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r)) ^ lam

/-- **Telescoping inverse-power series of gibonacci polynomials at even indices, odd shift.**
Let $x > 0$ be real, and let $g_n$ denote either the Fibonacci polynomials, given by $g_0 = 0$ and
$g_1 = 1$, or the Lucas polynomials, given by $g_0 = 2$ and $g_1 = x$, both satisfying
$g_{n+2} = x g_{n+1} + g_n$ and evaluated at $x$. Let $k$ be an odd natural number and
$\lambda$ a positive integer. Then
$$\sum_{n=0}^{\infty} \left(\frac{1}{g_{2n+2}^{\lambda}} - \frac{1}{g_{2n+2+2k}^{\lambda}}\right) =
\sum_{r=1}^{k} \frac{1}{g_{2r}^{\lambda}}.$$

The source quotes this lemma from Koshy as the sum over $n \ge (k + 1)/2$ of
$1/g_{2n+1-k}^{\lambda} - 1/g_{2n+1+k}^{\lambda}$; here the summation index is shifted to start
at $0$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.4 (`fq-2024-linzhou02172024-lem-2.4`). -/
public theorem_wanted tsum_inv_pow_gibonacciPoly_succ_sub_odd {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Odd k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 2)) ^ lam - 1 / aeval x (g (2 * n + 2 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r)) ^ lam

/-- **Telescoping inverse-power series of gibonacci polynomials at odd indices, even shift.**
Let $x > 0$ be real, and let $g_n$ denote either the Fibonacci polynomials, given by $g_0 = 0$ and
$g_1 = 1$, or the Lucas polynomials, given by $g_0 = 2$ and $g_1 = x$, both satisfying
$g_{n+2} = x g_{n+1} + g_n$ and evaluated at $x$. Let $k$ be an even natural number and
$\lambda$ a positive integer. Then
$$\sum_{n=0}^{\infty} \left(\frac{1}{g_{2n+1}^{\lambda}} - \frac{1}{g_{2n+1+2k}^{\lambda}}\right) =
\sum_{r=1}^{k} \frac{1}{g_{2r-1}^{\lambda}}.$$

The source quotes this lemma from Koshy as the sum over $n \ge k/2$ of
$1/g_{2n+1-k}^{\lambda} - 1/g_{2n+1+k}^{\lambda}$; here the summation index is shifted to start
at $0$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.5 (`fq-2024-linzhou02172024-lem-2.5`). -/
public theorem_wanted tsum_inv_pow_gibonacciPoly_succ_sub_even {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Even k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 1)) ^ lam - 1 / aeval x (g (2 * n + 1 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r - 1)) ^ lam

/-- **Even powers of Fibonacci polynomials at $n \pm k$.** Let $f_i \in \mathbb{Z}[x]$ be the
Fibonacci polynomials, defined by $f_0 = 0$, $f_1 = 1$ and $f_{i+2} = x f_{i+1} + f_i$. For all
natural numbers $k \le n$ and every natural number $m$,
$$
(x^2 + 4)^{m-1} \bigl(f_{n+k}^{2m} - f_{n-k}^{2m}\bigr) =
\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{(n+k+1)j} f_{2k(m-j)} f_{2n(m-j)}
$$
in $\mathbb{Z}[x]$, where for $m = 0$ the exponent $m - 1$ is read as $0$ (both sides are then
$0$).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 3.1 (`fq-2024-linzhou02172024-lem-3.1`). -/
public theorem_wanted fibPoly_pow_even_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (X ^ 2 + 4) ^ (m - 1) * (𝔣 (n + k) ^ (2 * m) - 𝔣 (n - k) ^ (2 * m)) =
      ∑ j ∈ Finset.range m, ((2 * m).choose j : ℤ[X]) * (-1) ^ ((n + k + 1) * j) *
        𝔣 (2 * k * (m - j)) * 𝔣 (2 * n * (m - j))

/-- **Even powers of Lucas polynomials at $n \pm k$.** Let $f_i$ and $\ell_i$ be the
Fibonacci and Lucas polynomials in $\mathbb{Z}[x]$, defined by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. For all natural numbers
$k \le n$ and every natural number $m$,
$$
\ell_{n+k}^{2m} - \ell_{n-k}^{2m} =
(x^2 + 4) \sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{(n+k)j} f_{2k(m-j)} f_{2n(m-j)}
$$
in $\mathbb{Z}[x]$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 3.2 (`fq-2024-linzhou02172024-lem-3.2`). -/
public theorem_wanted lucasPoly_pow_even_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    𝔩 (n + k) ^ (2 * m) - 𝔩 (n - k) ^ (2 * m) =
      (X ^ 2 + 4) * ∑ j ∈ Finset.range m, ((2 * m).choose j : ℤ[X]) * (-1) ^ ((n + k) * j) *
        𝔣 (2 * k * (m - j)) * 𝔣 (2 * n * (m - j))

/-- **Odd powers of Fibonacci polynomials at $n \pm k$.** Let $f_i$ and $\ell_i$ be the
Fibonacci and Lucas polynomials in $\mathbb{Z}[x]$, defined by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. Let $k \le n$ and $m$ be natural
numbers. In $\mathbb{Z}[x]$, if $k$ is odd then
$$
(x^2 + 4)^m \bigl(f_{n+k}^{2m+1} - f_{n-k}^{2m+1}\bigr) =
\sum_{j=0}^{m} \binom{2m+1}{j} (-1)^{nj} f_{n(2m+1-2j)} \ell_{k(2m+1-2j)},
$$
and if $k$ is even then
$$
(x^2 + 4)^m \bigl(f_{n+k}^{2m+1} - f_{n-k}^{2m+1}\bigr) =
\sum_{j=0}^{m} \binom{2m+1}{j} (-1)^{(n+1)j} \ell_{n(2m+1-2j)} f_{k(2m+1-2j)}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 4.1 (`fq-2024-linzhou02172024-lem-4.1`). -/
public theorem_wanted fibPoly_pow_odd_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (Odd k → (X ^ 2 + 4) ^ m * (𝔣 (n + k) ^ (2 * m + 1) - 𝔣 (n - k) ^ (2 * m + 1)) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) * (-1) ^ (n * j) *
        𝔣 (n * (2 * m + 1 - 2 * j)) * 𝔩 (k * (2 * m + 1 - 2 * j))) ∧
    (Even k → (X ^ 2 + 4) ^ m * (𝔣 (n + k) ^ (2 * m + 1) - 𝔣 (n - k) ^ (2 * m + 1)) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) * (-1) ^ ((n + 1) * j) *
        𝔩 (n * (2 * m + 1 - 2 * j)) * 𝔣 (k * (2 * m + 1 - 2 * j)))

/-- **Odd powers of Lucas polynomials at $n \pm k$.** Let $f_i$ and $\ell_i$ be the
Fibonacci and Lucas polynomials in $\mathbb{Z}[x]$, defined by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. Let $k \le n$ and $m$ be natural
numbers. In $\mathbb{Z}[x]$, if $k$ is odd then
$$
\ell_{n+k}^{2m+1} - \ell_{n-k}^{2m+1} =
\sum_{j=0}^{m} \binom{2m+1}{j} (-1)^{(n+1)j} \ell_{n(2m+1-2j)} \ell_{k(2m+1-2j)},
$$
and if $k$ is even then
$$
\ell_{n+k}^{2m+1} - \ell_{n-k}^{2m+1} =
(x^2 + 4) \sum_{j=0}^{m} \binom{2m+1}{j} (-1)^{nj} f_{n(2m+1-2j)} f_{k(2m+1-2j)}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 4.2 (`fq-2024-linzhou02172024-lem-4.2`). -/
public theorem_wanted lucasPoly_pow_odd_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (Odd k → 𝔩 (n + k) ^ (2 * m + 1) - 𝔩 (n - k) ^ (2 * m + 1) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) * (-1) ^ ((n + 1) * j) *
        𝔩 (n * (2 * m + 1 - 2 * j)) * 𝔩 (k * (2 * m + 1 - 2 * j))) ∧
    (Even k → 𝔩 (n + k) ^ (2 * m + 1) - 𝔩 (n - k) ^ (2 * m + 1) =
      (X ^ 2 + 4) * ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) *
        (-1) ^ (n * j) * 𝔣 (n * (2 * m + 1 - 2 * j)) * 𝔣 (k * (2 * m + 1 - 2 * j)))

/-- **Cubic-denominator series for even-index Fibonacci polynomials.** Let $f_i$ and $\ell_i$ be the
Fibonacci and Lucas polynomials, defined by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$, $\ell_1 = x$ and
$g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. For every real $x > 0$,
$$
\sum_{n \ge 1} \frac{(x^3 + 3x) f_{6n}(x) + 3x f_{2n}(x)}{(f_{2n}(x)^2 + 1)^3} = x^2 + 4
$$
and
$$
\sum_{n \ge 2} \frac{x(x^4 + 4x^2 + 3) \ell_{6n}(x) - 3x \ell_{2n}(x)}{(f_{2n}(x)^2 - x^2)^3} =
\frac{(x^2 + 4)\bigl((x^2 + 2)^3 + 1\bigr)}{x^3 (x^2 + 2)^3}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.3 (`fq-2024-linzhou02172024-cor-4.3`). -/
public theorem_wanted tsum_fibPoly_cube_even_index {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((x ^ 3 + 3 * x) * aeval x (𝔣 (6 * (n + 1))) + 3 * x * aeval x (𝔣 (2 * (n + 1)))) /
        (aeval x (𝔣 (2 * (n + 1))) ^ 2 + 1) ^ 3 =
      x ^ 2 + 4 ∧
      ∑' n : ℕ, (x * (x ^ 4 + 4 * x ^ 2 + 3) * aeval x (𝔩 (6 * (n + 2))) -
          3 * x * aeval x (𝔩 (2 * (n + 2)))) /
          (aeval x (𝔣 (2 * (n + 2))) ^ 2 - x ^ 2) ^ 3 =
        (x ^ 2 + 4) * ((x ^ 2 + 2) ^ 3 + 1) / (x ^ 3 * (x ^ 2 + 2) ^ 3)

/-- **Cubic series over even-indexed Lucas polynomials.** Let $x > 0$ be real, and let $f_n$ and
$\ell_n$ denote the Fibonacci and Lucas polynomials evaluated at $x$, given by $f_0 = 0$,
$f_1 = 1$, $\ell_0 = 2$, $\ell_1 = x$ and the recurrence $z_{n+2} = x z_{n+1} + z_n$ for both. Then
$$\sum_{n=1}^{\infty} \frac{(x^3 + 3x) \ell_{6n} - 3x \ell_{2n}}
{\left(\ell_{2n}^2 - (x^2 + 4)\right)^3} = \frac{1}{x^3}$$
and
$$\sum_{n=2}^{\infty} \frac{x(x^4 + 4x^2 + 3) f_{6n} + 3x f_{2n}}
{\left(\ell_{2n}^2 + (x^2 + 4) x^2\right)^3} =
\frac{1}{x^2 + 4} \left(\frac{1}{(x^2 + 2)^3} + \frac{1}{(x^4 + 4x^2 + 2)^3}\right).$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.5 (`fq-2024-linzhou02172024-cor-4.5`). -/
public theorem_wanted tsum_lucasPoly_cube_even_index {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((x ^ 3 + 3 * x) * aeval x (𝔩 (6 * (n + 1))) - 3 * x * aeval x (𝔩 (2 * (n + 1)))) /
        (aeval x (𝔩 (2 * (n + 1))) ^ 2 - (x ^ 2 + 4)) ^ 3 =
      1 / x ^ 3 ∧
      ∑' n : ℕ, (x * (x ^ 4 + 4 * x ^ 2 + 3) * aeval x (𝔣 (6 * (n + 2))) +
          3 * x * aeval x (𝔣 (2 * (n + 2)))) /
          (aeval x (𝔩 (2 * (n + 2))) ^ 2 + (x ^ 2 + 4) * x ^ 2) ^ 3 =
        1 / (x ^ 2 + 4) * (1 / (x ^ 2 + 2) ^ 3 + 1 / (x ^ 4 + 4 * x ^ 2 + 2) ^ 3)

/-- **Cubic-denominator series for odd-index Fibonacci polynomials.** Let $f_i$ and $\ell_i$ be the
Fibonacci and Lucas polynomials, defined by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$, $\ell_1 = x$ and
$g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. For every real $x > 0$,
$$
\sum_{n \ge 1} \frac{(x^3 + 3x) f_{6n+3}(x) - 3x f_{2n+1}(x)}{(f_{2n+1}(x)^2 - 1)^3} =
\frac{x^2 + 4}{x^3}
$$
and
$$
\sum_{n \ge 1} \frac{x(x^4 + 4x^2 + 3) \ell_{6n+3}(x) + 3x \ell_{2n+1}(x)}
{(f_{2n+1}(x)^2 + x^2)^3} =
\frac{(x^2 + 4)\bigl((x^2 + 1)^3 + 1\bigr)}{(x^2 + 1)^3}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.7 (`fq-2024-linzhou02172024-cor-4.7`). -/
public theorem_wanted tsum_fibPoly_cube_odd_index {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((x ^ 3 + 3 * x) * aeval x (𝔣 (6 * (n + 1) + 3)) -
          3 * x * aeval x (𝔣 (2 * (n + 1) + 1))) /
        (aeval x (𝔣 (2 * (n + 1) + 1)) ^ 2 - 1) ^ 3 =
      (x ^ 2 + 4) / x ^ 3 ∧
      ∑' n : ℕ, (x * (x ^ 4 + 4 * x ^ 2 + 3) * aeval x (𝔩 (6 * (n + 1) + 3)) +
          3 * x * aeval x (𝔩 (2 * (n + 1) + 1))) /
          (aeval x (𝔣 (2 * (n + 1) + 1)) ^ 2 + x ^ 2) ^ 3 =
        (x ^ 2 + 4) * ((x ^ 2 + 1) ^ 3 + 1) / (x ^ 2 + 1) ^ 3

/-- **Cubic sums with odd-index Lucas polynomial denominators.** Let $f_n$ and $\ell_n$ denote the
Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$, $\ell_1 = x$ and
$g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, \ell\}$, evaluated at a real number $x > 0$. Then
$$\sum_{n \ge 1} \frac{(x^3 + 3x) \ell_{6n+3} + 3x \ell_{2n+1}}{(\ell_{2n+1}^2 + x^2 + 4)^3}
= \frac{1}{(x^2 + 2)^3}$$
and
$$\sum_{n \ge 1} \frac{x (x^4 + 4x^2 + 3) f_{6n+3} - 3x f_{2n+1}}{(\ell_{2n+1}^2 - x^2 (x^2 + 4))^3}
= \frac{(x^2 + 3)^3 + 1}{x^3 (x^2 + 4) (x^2 + 3)^3}.$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.9 (`fq-2024-linzhou02172024-cor-4.9`). -/
public theorem_wanted tsum_lucasPoly_cube_odd_index {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((x ^ 3 + 3 * x) * aeval x (𝔩 (6 * (n + 1) + 3)) +
          3 * x * aeval x (𝔩 (2 * (n + 1) + 1))) /
        (aeval x (𝔩 (2 * (n + 1) + 1)) ^ 2 + x ^ 2 + 4) ^ 3 =
      1 / (x ^ 2 + 2) ^ 3 ∧
      ∑' n : ℕ, (x * (x ^ 4 + 4 * x ^ 2 + 3) * aeval x (𝔣 (6 * (n + 1) + 3)) -
          3 * x * aeval x (𝔣 (2 * (n + 1) + 1))) /
          (aeval x (𝔩 (2 * (n + 1) + 1)) ^ 2 - x ^ 2 * (x ^ 2 + 4)) ^ 3 =
        ((x ^ 2 + 3) ^ 3 + 1) / (x ^ 3 * (x ^ 2 + 4) * (x ^ 2 + 3) ^ 3)

/-- **Cubic-denominator series for even-index Fibonacci numbers.** Let $F_n$ be the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$) and $L_n$ the Lucas numbers. Then, as
series of real numbers,
$$
\sum_{n \ge 1} \frac{4F_{6n} + 3F_{2n}}{(F_{2n}^2 + 1)^3} = 5
\quad\text{and}\quad
\sum_{n \ge 2} \frac{8L_{6n} - 3L_{2n}}{(F_{2n}^2 - 1)^3} = \frac{140}{27}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.4 (`fq-2024-linzhou02172024-cor-4.4`). -/
public theorem_wanted tsum_fib_cube_even_index :
    ∑' n : ℕ, (4 * (Nat.fib (6 * (n + 1)) : ℝ) + 3 * (Nat.fib (2 * (n + 1)) : ℝ)) /
        ((Nat.fib (2 * (n + 1)) : ℝ) ^ 2 + 1) ^ 3 = 5 ∧
      ∑' n : ℕ, (8 * (lucasNumber (6 * (n + 2)) : ℝ) - 3 * (lucasNumber (2 * (n + 2)) : ℝ)) /
          ((Nat.fib (2 * (n + 2)) : ℝ) ^ 2 - 1) ^ 3 = 140 / 27

/-- **Cubic series over even-indexed Lucas numbers.** Let $F_n$ and $L_n$ denote the Fibonacci and
Lucas numbers, given by $F_0 = 0$, $F_1 = 1$, $L_0 = 2$, $L_1 = 1$ and the recurrence
$z_{n+2} = z_{n+1} + z_n$ for both. Then
$$\sum_{n=1}^{\infty} \frac{4L_{6n} - 3L_{2n}}{(L_{2n}^2 - 5)^3} = 1$$
and
$$\sum_{n=2}^{\infty} \frac{8F_{6n} + 3F_{2n}}{(L_{2n}^2 + 5)^3} = \frac{74}{9261}.$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.6 (`fq-2024-linzhou02172024-cor-4.6`). -/
public theorem_wanted tsum_lucas_cube_even_index :
    ∑' n : ℕ, (4 * (lucasNumber (6 * (n + 1)) : ℝ) - 3 * (lucasNumber (2 * (n + 1)) : ℝ)) /
        ((lucasNumber (2 * (n + 1)) : ℝ) ^ 2 - 5) ^ 3 = 1 ∧
      ∑' n : ℕ, (8 * (Nat.fib (6 * (n + 2)) : ℝ) + 3 * (Nat.fib (2 * (n + 2)) : ℝ)) /
          ((lucasNumber (2 * (n + 2)) : ℝ) ^ 2 + 5) ^ 3 = 74 / 9261

/-- **Cubic-denominator series for odd-index Fibonacci numbers.** Let $F_n$ be the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$) and $L_n$ the Lucas numbers. Then, as
series of real numbers,
$$
\sum_{n \ge 1} \frac{4F_{6n+3} - 3F_{2n+1}}{(F_{2n+1}^2 - 1)^3} = 5
\quad\text{and}\quad
\sum_{n \ge 1} \frac{8L_{6n+3} + 3L_{2n+1}}{(F_{2n+1}^2 + 1)^3} = \frac{45}{8}.
$$

These are the case $x = 1$ of Corollary 4.7. The extracted record of the source prints the lower
limit of the second series as $n = 2$; with that limit the sum would be
$45/8 - 124/25 = 133/200$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.8 (`fq-2024-linzhou02172024-cor-4.8`). -/
public theorem_wanted tsum_fib_cube_odd_index :
    ∑' n : ℕ, (4 * (Nat.fib (6 * (n + 1) + 3) : ℝ) - 3 * (Nat.fib (2 * (n + 1) + 1) : ℝ)) /
        ((Nat.fib (2 * (n + 1) + 1) : ℝ) ^ 2 - 1) ^ 3 = 5 ∧
      ∑' n : ℕ, (8 * (lucasNumber (6 * (n + 1) + 3) : ℝ) +
          3 * (lucasNumber (2 * (n + 1) + 1) : ℝ)) /
          ((Nat.fib (2 * (n + 1) + 1) : ℝ) ^ 2 + 1) ^ 3 = 45 / 8

/-- **Cubic series over odd-indexed Lucas numbers.** Let $F_n$ and $L_n$ denote the Fibonacci and
Lucas numbers, given by $F_0 = 0$, $F_1 = 1$, $L_0 = 2$, $L_1 = 1$ and the recurrence
$z_{n+2} = z_{n+1} + z_n$ for both. Then
$$\sum_{n=1}^{\infty} \frac{4L_{6n+3} + 3L_{2n+1}}{(L_{2n+1}^2 + 5)^3} = \frac{1}{27}$$
and
$$\sum_{n=1}^{\infty} \frac{8F_{6n+3} - 3F_{2n+1}}{(L_{2n+1}^2 - 5)^3} = \frac{13}{64}.$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.10 (`fq-2024-linzhou02172024-cor-4.10`). -/
public theorem_wanted tsum_lucas_cube_odd_index :
    ∑' n : ℕ, (4 * (lucasNumber (6 * (n + 1) + 3) : ℝ) + 3 * (lucasNumber (2 * (n + 1) + 1) : ℝ)) /
        ((lucasNumber (2 * (n + 1) + 1) : ℝ) ^ 2 + 5) ^ 3 = 1 / 27 ∧
      ∑' n : ℕ, (8 * (Nat.fib (6 * (n + 1) + 3) : ℝ) - 3 * (Nat.fib (2 * (n + 1) + 1) : ℝ)) /
          ((lucasNumber (2 * (n + 1) + 1) : ℝ) ^ 2 - 5) ^ 3 = 13 / 64

/-- **Series of even powers of Fibonacci polynomials at even indices.** Let $f_i$ be the
Fibonacci polynomials, defined by $f_0 = 0$, $f_1 = 1$ and $f_{i+2} = x f_{i+1} + f_i$. Let
$x > 0$ be real and let $k$ and $m$ be positive integers. If $k$ is odd, put $L = (k + 1)/2$ and
$s_r = 2r - 1$; if $k$ is even, put $L = k/2 + 1$ and $s_r = 2r$. Then
$$
\sum_{n \ge L} \frac{\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{(k+1)j} f_{2k(m-j)}(x)
f_{4n(m-j)}(x)}{\bigl(f_{2n}(x)^2 - (-1)^k f_k(x)^2\bigr)^{2m}} =
(x^2 + 4)^{m-1} \sum_{r=1}^{k} \frac{1}{f_{s_r}(x)^{2m}}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.1 (`fq-2024-linzhou02172024-thm-1.1`). -/
public theorem_wanted tsum_fibPoly_even_pow_even_index {x : ℝ} (hx : 0 < x) {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) :
    ∑' n : ℕ, (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ ((k + 1) * j) *
          aeval x (𝔣 (2 * k * (m - j))) * aeval x (𝔣 (4 * (n + 𝔏[k]) * (m - j)))) /
        (aeval x (𝔣 (2 * (n + 𝔏[k]))) ^ 2 - (-1) ^ k * aeval x (𝔣 k) ^ 2) ^ (2 * m) =
      (x ^ 2 + 4) ^ (m - 1) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 𝔰[k, r]) ^ (2 * m)

/-- **Even-power sums with even-index Lucas polynomial denominators.** Let $f_n$ and $\ell_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, \ell\}$, evaluated at a real number
$x > 0$, and let $k$ and $m$ be positive integers. Put $L = (k + 1)/2$ and $s_r = 2r - 1$ if $k$
is odd, and $L = k/2 + 1$ and $s_r = 2r$ if $k$ is even. Then
$$\sum_{n \ge L} \frac{\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{kj} f_{2k(m-j)} f_{4n(m-j)}}
{\left(\ell_{2n}^2 + (-1)^k (x^2 + 4) f_k^2\right)^{2m}}
= \frac{1}{x^2 + 4} \sum_{r=1}^{k} \frac{1}{\ell_{s_r}^{2m}}.$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.2 (`fq-2024-linzhou02172024-thm-1.2`). -/
public theorem_wanted tsum_lucasPoly_even_pow_even_index {x : ℝ} (hx : 0 < x) {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) :
    ∑' n : ℕ, (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ (k * j) *
          aeval x (𝔣 (2 * k * (m - j))) * aeval x (𝔣 (4 * (n + 𝔏[k]) * (m - j)))) /
        (aeval x (𝔩 (2 * (n + 𝔏[k]))) ^ 2 + (-1) ^ k * (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^ (2 * m) =
      1 / (x ^ 2 + 4) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 𝔰[k, r]) ^ (2 * m)

/-- **Even-power series over odd-indexed Fibonacci polynomials.** Let $x > 0$ be real, let $f_n$
denote the Fibonacci polynomials evaluated at $x$, given by $f_0 = 0$, $f_1 = 1$ and
$f_{n+2} = x f_{n+1} + f_n$, and let $k$ and $m$ be positive integers. Put $M = (k + 1)/2$ and
$t_r = 2r$ if $k$ is odd, and $M = k/2$ and $t_r = 2r - 1$ if $k$ is even. Then
$$\sum_{n=0}^{\infty} \frac{\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{kj} f_{2k(m-j)}
f_{(4(n+M)+2)(m-j)}}{\left(f_{2(n+M)+1}^2 + (-1)^k f_k^2\right)^{2m}} =
(x^2 + 4)^{m-1} \sum_{r=1}^{k} \frac{1}{f_{t_r}^{2m}}.$$

This is the source's sum over $n \ge M$ with the summation index shifted to start at $0$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.3 (`fq-2024-linzhou02172024-thm-1.3`). -/
public theorem_wanted tsum_fibPoly_even_pow_odd_index {x : ℝ} (hx : 0 < x) {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) :
    ∑' n : ℕ, (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ (k * j) *
          aeval x (𝔣 (2 * k * (m - j))) * aeval x (𝔣 ((4 * (n + 𝔐[k]) + 2) * (m - j)))) /
        (aeval x (𝔣 (2 * (n + 𝔐[k]) + 1)) ^ 2 + (-1) ^ k * aeval x (𝔣 k) ^ 2) ^ (2 * m) =
      (x ^ 2 + 4) ^ (m - 1) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 𝔱[k, r]) ^ (2 * m)

/-- **Even-power sums with odd-index Lucas polynomial denominators.** Let $f_n$ and $\ell_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, \ell\}$, evaluated at a real number
$x > 0$, and let $k$ and $m$ be positive integers. Put $M = (k + 1)/2$ and $t_r = 2r$ if $k$ is
odd, and $M = k/2$ and $t_r = 2r - 1$ if $k$ is even. Then
$$\sum_{n \ge M} \frac{\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{(k+1)j} f_{2k(m-j)} f_{(4n+2)(m-j)}}
{\left(\ell_{2n+1}^2 - (-1)^k (x^2 + 4) f_k^2\right)^{2m}}
= \frac{1}{x^2 + 4} \sum_{r=1}^{k} \frac{1}{\ell_{t_r}^{2m}}.$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.4 (`fq-2024-linzhou02172024-thm-1.4`). -/
public theorem_wanted tsum_lucasPoly_even_pow_odd_index {x : ℝ} (hx : 0 < x) {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) :
    ∑' n : ℕ, (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ ((k + 1) * j) *
          aeval x (𝔣 (2 * k * (m - j))) * aeval x (𝔣 ((4 * (n + 𝔐[k]) + 2) * (m - j)))) /
        (aeval x (𝔩 (2 * (n + 𝔐[k]) + 1)) ^ 2 - (-1) ^ k * (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^
          (2 * m) =
      1 / (x ^ 2 + 4) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 𝔱[k, r]) ^ (2 * m)

/-- **Odd-power series over even-indexed Fibonacci polynomials.** Let $x > 0$ be real, let $f_n$
and $\ell_n$ denote the Fibonacci and Lucas polynomials evaluated at $x$, given by $f_0 = 0$,
$f_1 = 1$, $\ell_0 = 2$, $\ell_1 = x$ and the recurrence $z_{n+2} = x z_{n+1} + z_n$ for both, and
let $k$ be a positive integer and $m$ a natural number. Put $L = (k + 1)/2$ if $k$ is odd and
$L = k/2 + 1$ if $k$ is even. If $k$ is odd, then
$$\sum_{n=0}^{\infty} \frac{\sum_{j=0}^{m} \binom{2m+1}{j} f_{2(n+L)(2m+1-2j)}
\ell_{k(2m+1-2j)}}{\left(f_{2(n+L)}^2 + f_k^2\right)^{2m+1}} =
(x^2 + 4)^m \sum_{r=1}^{k} \frac{1}{f_{2r-1}^{2m+1}},$$
and if $k$ is even, then
$$\sum_{n=0}^{\infty} \frac{\sum_{j=0}^{m} \binom{2m+1}{j} (-1)^j \ell_{2(n+L)(2m+1-2j)}
f_{k(2m+1-2j)}}{\left(f_{2(n+L)}^2 - f_k^2\right)^{2m+1}} =
(x^2 + 4)^m \sum_{r=1}^{k} \frac{1}{f_{2r}^{2m+1}}.$$

These are the source's sums over $n \ge L$ with the summation index shifted to start at $0$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.5 (`fq-2024-linzhou02172024-thm-1.5`). -/
public theorem_wanted tsum_fibPoly_odd_pow_even_index {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 0 < k) (m : ℕ) :
    (Odd k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) *
          aeval x (𝔣 (2 * (n + 𝔏[k]) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔩 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔣 (2 * (n + 𝔏[k]))) ^ 2 + aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      (x ^ 2 + 4) ^ m * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 (2 * r - 1)) ^ (2 * m + 1)) ∧
    (Even k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ j *
          aeval x (𝔩 (2 * (n + 𝔏[k]) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔣 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔣 (2 * (n + 𝔏[k]))) ^ 2 - aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      (x ^ 2 + 4) ^ m * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 (2 * r)) ^ (2 * m + 1))

/-- **Odd-power sums with even-index Lucas polynomial denominators.** Let $f_n$ and $\ell_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, \ell\}$, evaluated at a real number
$x > 0$, let $k$ be a positive integer and $m$ a natural number, and put $L = (k + 1)/2$ if $k$ is
odd and $L = k/2 + 1$ if $k$ is even. If $k$ is odd, then
$$\sum_{n \ge L} \frac{\sum_{j=0}^{m} (-1)^j \binom{2m+1}{j} \ell_{2n(2m+1-2j)} \ell_{k(2m+1-2j)}}
{\left(\ell_{2n}^2 - (x^2 + 4) f_k^2\right)^{2m+1}}
= \sum_{r=1}^{k} \frac{1}{\ell_{2r-1}^{2m+1}},$$
and if $k$ is even, then
$$\sum_{n \ge L} \frac{\sum_{j=0}^{m} \binom{2m+1}{j} f_{2n(2m+1-2j)} f_{k(2m+1-2j)}}
{\left(\ell_{2n}^2 + (x^2 + 4) f_k^2\right)^{2m+1}}
= \frac{1}{x^2 + 4} \sum_{r=1}^{k} \frac{1}{\ell_{2r}^{2m+1}}.$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.6 (`fq-2024-linzhou02172024-thm-1.6`). -/
public theorem_wanted tsum_lucasPoly_odd_pow_even_index {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 0 < k) (m : ℕ) :
    (Odd k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ j *
          aeval x (𝔩 (2 * (n + 𝔏[k]) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔩 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔩 (2 * (n + 𝔏[k]))) ^ 2 - (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 (2 * r - 1)) ^ (2 * m + 1)) ∧
    (Even k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) *
          aeval x (𝔣 (2 * (n + 𝔏[k]) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔣 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔩 (2 * (n + 𝔏[k]))) ^ 2 + (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      1 / (x ^ 2 + 4) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 (2 * r)) ^ (2 * m + 1))

/-- **Odd-power series over odd-indexed Fibonacci polynomials.** Let $x > 0$ be real, let $f_n$
and $\ell_n$ denote the Fibonacci and Lucas polynomials evaluated at $x$, given by $f_0 = 0$,
$f_1 = 1$, $\ell_0 = 2$, $\ell_1 = x$ and the recurrence $z_{n+2} = x z_{n+1} + z_n$ for both, and
let $k$ be a positive integer and $m$ a natural number. Put $M = (k + 1)/2$ if $k$ is odd and
$M = k/2$ if $k$ is even. If $k$ is odd, then
$$\sum_{n=0}^{\infty} \frac{\sum_{j=0}^{m} \binom{2m+1}{j} (-1)^j f_{(2(n+M)+1)(2m+1-2j)}
\ell_{k(2m+1-2j)}}{\left(f_{2(n+M)+1}^2 - f_k^2\right)^{2m+1}} =
(x^2 + 4)^m \sum_{r=1}^{k} \frac{1}{f_{2r}^{2m+1}},$$
and if $k$ is even, then
$$\sum_{n=0}^{\infty} \frac{\sum_{j=0}^{m} \binom{2m+1}{j} \ell_{(2(n+M)+1)(2m+1-2j)}
f_{k(2m+1-2j)}}{\left(f_{2(n+M)+1}^2 + f_k^2\right)^{2m+1}} =
(x^2 + 4)^m \sum_{r=1}^{k} \frac{1}{f_{2r-1}^{2m+1}}.$$

These are the source's sums over $n \ge M$ with the summation index shifted to start at $0$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.7 (`fq-2024-linzhou02172024-thm-1.7`). -/
public theorem_wanted tsum_fibPoly_odd_pow_odd_index {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 0 < k) (m : ℕ) :
    (Odd k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ j *
          aeval x (𝔣 ((2 * (n + 𝔐[k]) + 1) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔩 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔣 (2 * (n + 𝔐[k]) + 1)) ^ 2 - aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      (x ^ 2 + 4) ^ m * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 (2 * r)) ^ (2 * m + 1)) ∧
    (Even k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) *
          aeval x (𝔩 ((2 * (n + 𝔐[k]) + 1) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔣 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔣 (2 * (n + 𝔐[k]) + 1)) ^ 2 + aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      (x ^ 2 + 4) ^ m * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 (2 * r - 1)) ^ (2 * m + 1))

/-- **Odd-power sums with odd-index Lucas polynomial denominators.** Let $f_n$ and $\ell_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, \ell\}$, evaluated at a real number
$x > 0$, let $k$ be a positive integer and $m$ a natural number, and put $M = (k + 1)/2$ if $k$ is
odd and $M = k/2$ if $k$ is even. If $k$ is odd, then
$$\sum_{n \ge M} \frac{\sum_{j=0}^{m} \binom{2m+1}{j} \ell_{(2n+1)(2m+1-2j)} \ell_{k(2m+1-2j)}}
{\left(\ell_{2n+1}^2 + (x^2 + 4) f_k^2\right)^{2m+1}}
= \sum_{r=1}^{k} \frac{1}{\ell_{2r}^{2m+1}},$$
and if $k$ is even, then
$$\sum_{n \ge M} \frac{\sum_{j=0}^{m} (-1)^j \binom{2m+1}{j} f_{(2n+1)(2m+1-2j)} f_{k(2m+1-2j)}}
{\left(\ell_{2n+1}^2 - (x^2 + 4) f_k^2\right)^{2m+1}}
= \frac{1}{x^2 + 4} \sum_{r=1}^{k} \frac{1}{\ell_{2r-1}^{2m+1}}.$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.8 (`fq-2024-linzhou02172024-thm-1.8`). -/
public theorem_wanted tsum_lucasPoly_odd_pow_odd_index {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 0 < k) (m : ℕ) :
    (Odd k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) *
          aeval x (𝔩 ((2 * (n + 𝔐[k]) + 1) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔩 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔩 (2 * (n + 𝔐[k]) + 1)) ^ 2 + (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^
          (2 * m + 1) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 (2 * r)) ^ (2 * m + 1)) ∧
    (Even k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ j *
          aeval x (𝔣 ((2 * (n + 𝔐[k]) + 1) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔣 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔩 (2 * (n + 𝔐[k]) + 1)) ^ 2 - (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      1 / (x ^ 2 + 4) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 (2 * r - 1)) ^ (2 * m + 1))

end

end MetaMathlibExt
