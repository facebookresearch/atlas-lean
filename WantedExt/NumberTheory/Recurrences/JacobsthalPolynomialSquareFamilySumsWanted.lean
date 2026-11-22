/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums involving a family of Jacobsthal polynomial squares

Statements from Thomas Koshy and Zhenguang Gao, *Sums Involving a Family of Jacobsthal Polynomial
Squares*, The Fibonacci Quarterly 62 (2024), Article koshy12202023.

The Fibonacci and Lucas polynomials `f_n`, `l_n` (`z_{n+2} = x z_{n+1} + z_n`, initial values
`0, 1` and `2, x`) and the Jacobsthal and Jacobsthal-Lucas polynomials `J_n`, `j_n`
(`z_{n+2} = z_{n+1} + x z_n`, initial values `0, 1` and `2, 1`) are the existing
`generalizedFibonacciPolynomial` sequences over `ℤ[X]`, evaluated at real `x > 0` with
`Polynomial.aeval`. As in the paper, `Δ = √(x² + 4)`, `α = (x + Δ)/2`, `D = √(4x + 1)` and
`w = (1 + D)/2`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- The Fibonacci polynomials `f_n(x)`. -/
local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1

/-- The Lucas polynomials `l_n(x)`. -/
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

/-- The Jacobsthal polynomials `J_n(x)`. -/
local notation "𝔍" => generalizedFibonacciPolynomial 0 1 1 X

/-- The Jacobsthal-Lucas polynomials `j_n(x)`. -/
local notation "𝔧" => generalizedFibonacciPolynomial 2 1 1 X

/-- **Reciprocal sums of shifted squares of Fibonacci and Lucas polynomials (Koshy–Gao,
Theorem 2.1).** Let $f_n(x)$ and $l_n(x)$ be the Fibonacci and Lucas polynomials, given by
$z_{n+2} = x z_{n+1} + z_n$ with initial values $f_0 = 0$, $f_1 = 1$ and $l_0 = 2$, $l_1 = x$.
Let $x > 0$ be real, let $k$, $p$, $r$, $t$ be positive integers with $t \le 2p$, and let
$\alpha = (x + \sqrt{x^2 + 4})/2$. Then
$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk} f_r(x) f_{2pk}(x)}
{f_{(2pn+p+t)k}(x)^2 - (-1)^{tk} f_{pk}(x)^2} =
\frac{f_{tk+r}(x)}{f_{tk}(x)} - \alpha^r
$$
and
$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk+1} (x^2 + 4) f_r(x) f_{2pk}(x)}
{l_{(2pn+p+t)k}(x)^2 + (-1)^{tk} (x^2 + 4) f_{pk}(x)^2} =
\frac{l_{tk+r}(x)}{l_{tk}(x)} - \alpha^r.
$$

In the source the sums run over $n \ge 1$, with $(2pn + t - p)k$ in place of $(2pn + p + t)k$;
here the summation index is shifted to start at $n = 0$.

Source: Thomas Koshy and Zhenguang Gao, *Sums Involving a Family of Jacobsthal Polynomial
Squares*, The Fibonacci Quarterly 62 (2024), Article koshy12202023,
Theorem 2.1 (`fq-2024-koshy12202023-thm-2.1`). -/
public theorem_wanted tsum_gibonacciPoly_sq_sub_family {x : ℝ} (hx : 0 < x) {k p r t : ℕ}
    (hk : 0 < k) (hp : 0 < p) (hr : 0 < r) (ht₀ : 0 < t) (ht : t ≤ 2 * p) :
    ∑' n : ℕ, (-1) ^ (t * k) * aeval x (𝔣 r) * aeval x (𝔣 (2 * p * k)) /
        (aeval x (𝔣 ((2 * p * n + p + t) * k)) ^ 2 - (-1) ^ (t * k) * aeval x (𝔣 (p * k)) ^ 2) =
      aeval x (𝔣 (t * k + r)) / aeval x (𝔣 (t * k)) - ((x + √(x ^ 2 + 4)) / 2) ^ r ∧
    ∑' n : ℕ, (-1) ^ (t * k + 1) * (x ^ 2 + 4) * aeval x (𝔣 r) * aeval x (𝔣 (2 * p * k)) /
        (aeval x (𝔩 ((2 * p * n + p + t) * k)) ^ 2 +
          (-1) ^ (t * k) * (x ^ 2 + 4) * aeval x (𝔣 (p * k)) ^ 2) =
      aeval x (𝔩 (t * k + r)) / aeval x (𝔩 (t * k)) - ((x + √(x ^ 2 + 4)) / 2) ^ r

/-- **Reciprocal sums of shifted squares of Jacobsthal and Jacobsthal–Lucas polynomials
(Koshy–Gao, Theorem 3.1).** Let $J_n(x)$ and $j_n(x)$ be the Jacobsthal and Jacobsthal–Lucas
polynomials, given by $z_{n+2} = z_{n+1} + x z_n$ with initial values $J_0 = 0$, $J_1 = 1$ and
$j_0 = 2$, $j_1 = 1$. Let $x > 0$ be real, let $k$, $p$, $r$, $t$ be positive integers with
$t \le 2p$, let $w = (1 + \sqrt{4x + 1})/2$, and write $e_n = (2pn + t)k$. Then
$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk} x^{e_n} J_r(x) J_{2pk}(x)}
{J_{(2pn+p+t)k}(x)^2 - (-1)^{tk} x^{e_n} J_{pk}(x)^2} =
\frac{J_{tk+r}(x)}{J_{tk}(x)} - w^r
$$
and
$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk+1} (4x + 1) x^{e_n} J_r(x) J_{2pk}(x)}
{j_{(2pn+p+t)k}(x)^2 + (-1)^{tk} (4x + 1) x^{e_n} J_{pk}(x)^2} =
\frac{j_{tk+r}(x)}{j_{tk}(x)} - w^r.
$$

In the source the sums run over $n \ge 1$, with $(2pn + t - p)k$ in place of $(2pn + p + t)k$
and exponent $(2pn + t - 2p)k$ in place of $e_n$; here the summation index is shifted to start
at $n = 0$.

Source: Thomas Koshy and Zhenguang Gao, *Sums Involving a Family of Jacobsthal Polynomial
Squares*, The Fibonacci Quarterly 62 (2024), Article koshy12202023,
Theorem 3.1 (`fq-2024-koshy12202023-thm-3.1`). -/
public theorem_wanted tsum_jacobsthalPoly_sq_sub_family {x : ℝ} (hx : 0 < x) {k p r t : ℕ}
    (hk : 0 < k) (hp : 0 < p) (hr : 0 < r) (ht₀ : 0 < t) (ht : t ≤ 2 * p) :
    ∑' n : ℕ, (-1) ^ (t * k) * x ^ ((2 * p * n + t) * k) * aeval x (𝔍 r) *
          aeval x (𝔍 (2 * p * k)) /
        (aeval x (𝔍 ((2 * p * n + p + t) * k)) ^ 2 -
          (-1) ^ (t * k) * x ^ ((2 * p * n + t) * k) * aeval x (𝔍 (p * k)) ^ 2) =
      aeval x (𝔍 (t * k + r)) / aeval x (𝔍 (t * k)) - ((1 + √(4 * x + 1)) / 2) ^ r ∧
    ∑' n : ℕ, (-1) ^ (t * k + 1) * (4 * x + 1) * x ^ ((2 * p * n + t) * k) * aeval x (𝔍 r) *
          aeval x (𝔍 (2 * p * k)) /
        (aeval x (𝔧 ((2 * p * n + p + t) * k)) ^ 2 +
          (-1) ^ (t * k) * (4 * x + 1) * x ^ ((2 * p * n + t) * k) * aeval x (𝔍 (p * k)) ^ 2) =
      aeval x (𝔧 (t * k + r)) / aeval x (𝔧 (t * k)) - ((1 + √(4 * x + 1)) / 2) ^ r

end

end MetaMathlibExt
