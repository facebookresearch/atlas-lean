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

/-- Lemma 2.1: for `x > 0`, `g ∈ {f, l}` and positive integers `k`, `λ`,
`Σ_{n ≥ 1} (g_{(2n-1)k+r}^λ / g_{(2n-1)k}^λ - g_{(2n+1)k+r}^λ / g_{(2n+1)k}^λ)`
`= g_{k+r}^λ / g_k^λ - α^{rλ}`.
The paper also asks `r, λ > 0`; at `r = 0` or `λ = 0` every term and the right side vanish, so
those hypotheses are dropped.

Source: Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Lemma 2.1. -/
public theorem_wanted tsum_gibonacciPoly_pow_ratio_telescope {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k : ℕ} (hk : 0 < k) (r lam : ℕ) :
    ∑' n : ℕ, (aeval x (g ((2 * n + 1) * k + r)) ^ lam / aeval x (g ((2 * n + 1) * k)) ^ lam -
        aeval x (g ((2 * n + 3) * k + r)) ^ lam / aeval x (g ((2 * n + 3) * k)) ^ lam) =
      aeval x (g (k + r)) ^ lam / aeval x (g k) ^ lam - ((x + √(x ^ 2 + 4)) / 2) ^ (r * lam)

/-- Lemma 2.2: for `x > 0`, `g ∈ {f, l}` and positive integers `k`, `λ`,
`Σ_{n ≥ 1} (g_{(2n-1)k}^λ / g_{(2n-1)k+r}^λ - g_{(2n+1)k}^λ / g_{(2n+1)k+r}^λ)`
`= g_k^λ / g_{k+r}^λ - (-β)^{rλ}`.
The paper also asks `r, λ > 0`; at `r = 0` or `λ = 0` both sides vanish, so those hypotheses are
dropped.

Source: Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Lemma 2.2. -/
public theorem_wanted tsum_gibonacciPoly_pow_inv_ratio_telescope {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k : ℕ} (hk : 0 < k) (r lam : ℕ) :
    ∑' n : ℕ, (aeval x (g ((2 * n + 1) * k)) ^ lam / aeval x (g ((2 * n + 1) * k + r)) ^ lam -
        aeval x (g ((2 * n + 3) * k)) ^ lam / aeval x (g ((2 * n + 3) * k + r)) ^ lam) =
      aeval x (g k) ^ lam / aeval x (g (k + r)) ^ lam - (-((x - √(x ^ 2 + 4)) / 2)) ^ (r * lam)

/-- Theorem 3.1, corrected sign: for `x > 0`, positive `k` and `g ∈ {f, l}` with
`(μ, ν) = (1, -1)` for `g = f` and `(Δ², 1)` for `g = l`,
`Σ_{n ≥ 1} (-1)^{k+1} μ ν f_r f_{2k} / (g_{2nk}² + (-1)^k μ ν f_k²) = g_{k+r}/g_k - α^r`.
The record prints the numerator as `(-1)^k μ ν f_r f_{2k}`, which negates the left side and is
false (`x = 1`, `g = f`, `k = r = 1`: the printed sum is `Σ 1/(F_{2n}² + 1) = (√5 - 1)/2`, the right
side is `1 - (1 + √5)/2`); the paper's proof (displays for `g = f` and `g = l`) and its `r = 1`
corollaries (`Σ 1/(F_{2n}² + 1) = -1/2 + √5/2`) use `(-1)^{k+1} μ ν`, which is stated. The paper
also asks `r > 0`; at `r = 0` both sides vanish.

Source: Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Theorem 3.1. -/
public theorem_wanted tsum_fib_mul_div_gibonacciPoly_sq_add {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} {μ ν : ℝ}
    (hg : (g = 𝔣 ∧ μ = 1 ∧ ν = -1) ∨ (g = 𝔩 ∧ μ = x ^ 2 + 4 ∧ ν = 1)) {k : ℕ} (hk : 0 < k)
    (r : ℕ) :
    ∑' n : ℕ, (-1) ^ (k + 1) * μ * ν * aeval x (𝔣 r) * aeval x (𝔣 (2 * k)) /
        (aeval x (g (2 * (n + 1) * k)) ^ 2 + (-1) ^ k * μ * ν * aeval x (𝔣 k) ^ 2) =
      aeval x (g (k + r)) / aeval x (g k) - ((x + √(x ^ 2 + 4)) / 2) ^ r

/-- Theorem 3.2: for `x > 0`, positive `k` and `g ∈ {f, l}` with `(μ, ν) = (1, -1)` for `g = f`
and `(Δ², 1)` for `g = l`,
`Σ_{n ≥ 1} (-1)^k μ ν f_r f_{2k} / (g_{2nk+r}² + (-1)^{r+k} μ ν f_k²) = g_k/g_{k+r} - (-β)^r`.
The paper also asks `r > 0`; at `r = 0` both sides vanish.

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
