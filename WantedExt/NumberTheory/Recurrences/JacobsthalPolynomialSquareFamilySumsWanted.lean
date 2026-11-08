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

/-- Theorem 2.1 (quoted from Koshy): for real `x > 0` and positive integers `k`, `p`, `r`, `t`
with `t ≤ 2p`, `α = (x + √(x² + 4))/2` and `g ∈ {f, l}`,
`Σ_{n≥1} (-1)^{tk} μ ν* f_r f_{2pk} / (g_{(2pn+t-p)k}² - (-1)^{tk} μ ν* f_{pk}²)
  = g_{tk+r}/g_{tk} - α^r`, where `μ ν* = 1` for `g = f` and `μ ν* = -(x² + 4)` for `g = l`
(the two cases as a conjunction; summation index shifted to start at `0`).

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

/-- Theorem 3.1: for real `x > 0` and positive integers `k`, `p`, `r`, `t` with `t ≤ 2p`,
`w = (1 + √(4x + 1))/2` and `c ∈ {J, j}`,
`Σ_{n≥1} (-1)^{tk} D* ν* x^{(2pn+t-2p)k} J_r J_{2pk} /
  (c_{(2pn+t-p)k}² - (-1)^{tk} D* ν* x^{(2pn+t-2p)k} J_{pk}²) = c_{tk+r}/c_{tk} - w^r`, where
`D* ν* = 1` for `c = J` and `D* ν* = -(4x + 1)` for `c = j` (the two cases as a conjunction;
summation index shifted to start at `0`).

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
