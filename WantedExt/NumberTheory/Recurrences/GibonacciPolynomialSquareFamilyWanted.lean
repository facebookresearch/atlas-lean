/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums involving a family of gibonacci polynomial squares

Statements from Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares:
Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023.

The Fibonacci polynomials `f_n(x)` (`f_0 = 0`, `f_1 = 1`) and Lucas polynomials `l_n(x)`
(`l_0 = 2`, `l_1 = x`), both with `z_{n+2} = x z_{n+1} + z_n`, are the existing
`generalizedFibonacciPolynomial` sequences over `ℤ[X]`, evaluated at a real `x` with
`Polynomial.aeval`; `g_n` is `f_n` or `l_n`, `Δ = √(x² + 4)` and `α = (x + Δ)/2`. The paper takes
`x` an arbitrary integer; the statements need `x > 0`: at `x = 0` the denominators `f_{2m}(0)`
vanish, and for `x < 0` the ratio `g_{m+r}/g_m` tends to `((x - Δ)/2)^r`, not `α^r`
(`x = -1`, `k = p = r = t = λ = 1`, `g = f`: the sum in Lemma 2.1 is `(√5 - 1)/2`, the right side
`-(1 + √5)/2`). They are stated for real `x > 0`, which contains the positive integers.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **A telescoping series of powers of gibonacci polynomial ratios.** Let $x > 0$ be real, let
$\alpha = (x + \sqrt{x^2 + 4})/2$, and let $g_n$ be either the Fibonacci polynomials $f_n(x)$,
given by $f_0 = 0$ and $f_1 = 1$, or the Lucas polynomials $l_n(x)$, given by $l_0 = 2$ and
$l_1 = x$, where both satisfy $z_{n+2} = x z_{n+1} + z_n$. Let $k$, $r$, $t$, $\lambda$ be positive
integers and $p$ a natural number with $t \le 2p$. Then the series
$$\sum_{n=1}^{\infty} \left[ \left( \frac{g_{(2pn+t-2p)k+r}}{g_{(2pn+t-2p)k}} \right)^{\lambda} -
\left( \frac{g_{(2pn+t)k+r}}{g_{(2pn+t)k}} \right)^{\lambda} \right]$$
converges unconditionally, and its sum is
$\left( g_{tk+r} / g_{tk} \right)^{\lambda} - \alpha^{\lambda r}$.

The source takes $x$ to be an integer; the statement is made for real $x > 0$, which contains the
positive integers.

Source: Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares:
Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023, Lemma 2.1
(`fq-2024-koshy11112023-lem-2.1`). -/
public theorem_wanted hasSum_gibonacciPoly_pow_ratio_telescoping (g : ℕ → ℤ[X])
    (hg : g = generalizedFibonacciPolynomial 0 1 X 1 ∨ g = generalizedFibonacciPolynomial 2 X X 1)
    {x : ℝ} (hx : 0 < x) {k p r t m : ℕ} (hk : 0 < k) (hr : 0 < r) (ht : 0 < t) (hm : 0 < m)
    (htp : t ≤ 2 * p) :
    HasSum (fun n : ℕ =>
        (aeval x (g ((2 * p * (n + 1) + t - 2 * p) * k + r)) /
            aeval x (g ((2 * p * (n + 1) + t - 2 * p) * k))) ^ m -
          (aeval x (g ((2 * p * (n + 1) + t) * k + r)) /
            aeval x (g ((2 * p * (n + 1) + t) * k))) ^ m)
      ((aeval x (g (t * k + r)) / aeval x (g (t * k))) ^ m -
        ((x + Real.sqrt (x ^ 2 + 4)) / 2) ^ (m * r))

/-- **Series over a family of Fibonacci polynomial squares.** Let $x > 0$ be real, let
$\alpha = (x + \sqrt{x^2 + 4})/2$, and let $f_n = f_n(x)$ be the Fibonacci polynomials, given by
$f_0 = 0$, $f_1 = 1$ and $f_{n+2} = x f_{n+1} + f_n$, evaluated at $x$. Let $k$, $r$, $t$ be
positive integers and $p$ a natural number with $t \le 2p$. Then the series
$$\sum_{n=1}^{\infty} \frac{(-1)^{tk} f_r f_{2pk}}{f_{(2pn+t-p)k}^2 - (-1)^{tk} f_{pk}^2}$$
converges unconditionally, and its sum is $f_{tk+r} / f_{tk} - \alpha^r$.

This is the Fibonacci-polynomial case of Theorem 3.1 of the source. The source takes $x$ to be an
integer; the statement is made for real $x > 0$, which contains the positive integers.

Source: Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares:
Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023, Theorem 3.1
(`fq-2024-koshy11112023-thm-3.1`). -/
public theorem_wanted hasSum_fibPoly_sq_family {x : ℝ} (hx : 0 < x) {k p r t : ℕ} (hk : 0 < k)
    (hr : 0 < r) (ht : 0 < t) (htp : t ≤ 2 * p) :
    HasSum (fun n : ℕ =>
        (-1) ^ (t * k) * aeval x (generalizedFibonacciPolynomial 0 1 X 1 r) *
            aeval x (generalizedFibonacciPolynomial 0 1 X 1 (2 * p * k)) /
          (aeval x (generalizedFibonacciPolynomial 0 1 X 1 ((2 * p * (n + 1) + t - p) * k)) ^ 2 -
            (-1) ^ (t * k) * aeval x (generalizedFibonacciPolynomial 0 1 X 1 (p * k)) ^ 2))
      (aeval x (generalizedFibonacciPolynomial 0 1 X 1 (t * k + r)) /
          aeval x (generalizedFibonacciPolynomial 0 1 X 1 (t * k)) -
        ((x + Real.sqrt (x ^ 2 + 4)) / 2) ^ r)

/-- **Series over a family of Lucas polynomial squares.** Let $x > 0$ be real, let
$\Delta = \sqrt{x^2 + 4}$ and $\alpha = (x + \Delta)/2$, and let $f_n$ and $l_n$ be the
Fibonacci and Lucas polynomials evaluated at $x$, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$,
$l_1 = x$ and the recurrence $z_{n+2} = x z_{n+1} + z_n$ for both. Let $k$, $r$, $t$ be positive
integers and $p$ a natural number with $t \le 2p$. Then the series
$$\sum_{n=1}^{\infty} \frac{-(-1)^{tk} \Delta^2 f_r f_{2pk}}
{l_{(2pn+t-p)k}^2 + (-1)^{tk} \Delta^2 f_{pk}^2}$$
converges unconditionally, and its sum is $l_{tk+r} / l_{tk} - \alpha^r$.

This is the Lucas-polynomial case of Theorem 3.1 of the source. The source takes $x$ to be an
integer; the statement is made for real $x > 0$, which contains the positive integers.

Source: Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares:
Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023, Theorem 3.1
(`fq-2024-koshy11112023-thm-3.1`). -/
public theorem_wanted hasSum_lucasPoly_sq_family {x : ℝ} (hx : 0 < x) {k p r t : ℕ}
    (hk : 0 < k) (hr : 0 < r) (ht : 0 < t) (htp : t ≤ 2 * p) :
    HasSum (fun n : ℕ =>
        (-1) ^ (t * k) * (-(x ^ 2 + 4)) * aeval x (generalizedFibonacciPolynomial 0 1 X 1 r) *
            aeval x (generalizedFibonacciPolynomial 0 1 X 1 (2 * p * k)) /
          (aeval x (generalizedFibonacciPolynomial 2 X X 1 ((2 * p * (n + 1) + t - p) * k)) ^ 2 -
            (-1) ^ (t * k) * (-(x ^ 2 + 4)) *
              aeval x (generalizedFibonacciPolynomial 0 1 X 1 (p * k)) ^ 2))
      (aeval x (generalizedFibonacciPolynomial 2 X X 1 (t * k + r)) /
          aeval x (generalizedFibonacciPolynomial 2 X X 1 (t * k)) -
        ((x + Real.sqrt (x ^ 2 + 4)) / 2) ^ r)

end

end MetaMathlibExt
