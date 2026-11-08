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

/-- Lemma 2.1: for positive integers `k`, `r`, `t`, `m = λ`, `p` with `t ≤ 2p`, real `x > 0` and
`g_n = f_n(x)` or `l_n(x)`,
`∑_{n ≥ 1} [g^λ_{(2pn+t-2p)k+r} / g^λ_{(2pn+t-2p)k} - g^λ_{(2pn+t)k+r} / g^λ_{(2pn+t)k}]
  = g^λ_{tk+r} / g^λ_{tk} - α^{λr}`,
as a `HasSum` over `n + 1`. The paper's integer `x` is replaced by real `x > 0` (see the module
docstring for `x ≤ 0`); `p ≥ 1` follows from `1 ≤ t ≤ 2p`.

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

/-- Theorem 3.1, Fibonacci-polynomial case (`μ = ν* = 1`): for positive integers `k`, `r`, `t`,
`p` with `t ≤ 2p` and real `x > 0`,
`∑_{n ≥ 1} (-1)^{tk} f_r f_{2pk} / (f²_{(2pn+t-p)k} - (-1)^{tk} f²_{pk}) = f_{tk+r}/f_{tk} - α^r`,
as a `HasSum` over `n + 1`. The paper's integer `x` is replaced by real `x > 0`.

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

/-- Theorem 3.1, Lucas-polynomial case (`μ = Δ²`, `ν* = -1`): for positive integers `k`, `r`,
`t`, `p` with `t ≤ 2p` and real `x > 0`,
`∑_{n ≥ 1} (-1)^{tk} μν* f_r f_{2pk} / (l²_{(2pn+t-p)k} - (-1)^{tk} μν* f²_{pk})
  = l_{tk+r}/l_{tk} - α^r` with `μν* = -(x² + 4)`, as a `HasSum` over `n + 1`. The paper's integer
`x` is replaced by real `x > 0`.

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
