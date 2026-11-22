/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Explicit bounds for counting gleeful representations

Statements from Sara Moore and Jonathan P. Sorenson, *Explicit Bounds and Parallel
Algorithms for Counting Multiply Gleeful Numbers*, INTEGERS 26 (2026), Article A84
(arXiv `2507.09012`, TeX source read).

A positive integer is `k`-gleeful when it is a sum of `k`th powers of consecutive
primes. With `p_{i+1} = Nat.nth Nat.Prime i`, the number `s_k(x)` of `k`-gleeful
representations of integers `≤ x` is the number of chains `(n, m)`, `m ≥ 1`, with
`p_{n+1}^k + ⋯ + p_{n+m}^k ≤ x`. The maximal chain length `M = M(x, k)` is
characterised by the paper's equation (1),
`2^k + 3^k + ⋯ + p_M^k ≤ x < 2^k + 3^k + ⋯ + p_{M+1}^k`, so `M ≥ M₀` means
`2^k + ⋯ + p_{M₀}^k ≤ x`. The constants `A, B, C, D, E, F, U, L, c_k` are the
paper's displayed functions evaluated at `y = M₀`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Upper bound for the maximal gleeful chain length.** Let $p_1 = 2, p_2 = 3, \dots$ be the
primes in increasing order. Let $k > 1$, $M_0 \ge 6$, $M \ge M_0$ and $x$ be natural numbers with
$p_1^k + \cdots + p_M^k \le x < p_1^k + \cdots + p_{M+1}^k$. Put $y = M_0$,
$$B = \frac{\log(y+1)}{\log y} + \frac{\log\log((y+1)^2)}{\log y} \cdot \frac{k}{k+1}$$
and $C = (y/(y-1))^{1/(k+1)} B^{k/(k+1)}$, where $\log$ is the natural logarithm. Then
$$M < 4^{1/(k+1)} \cdot \frac{(k+1)\, x^{1/(k+1)}}{(\log x)^{k/(k+1)}} \cdot C.$$

Source: Sara Moore and Jonathan P. Sorenson, *Explicit Bounds and Parallel
Algorithms for Counting Multiply Gleeful Numbers*, INTEGERS 26 (2026), Article A84,
Lemma 1 (`integers-2026-A84-lem-1`), with `B`, `C` from Section 2. -/
public theorem_wanted maxChainLength_lt (k M₀ M x : ℕ) (hk : 1 < k) (hM₀ : 6 ≤ M₀)
    (hM : M₀ ≤ M) (hx : ∑ i ∈ Finset.range M, Nat.nth Nat.Prime i ^ k ≤ x)
    (hx' : x < ∑ i ∈ Finset.range (M + 1), Nat.nth Nat.Prime i ^ k) :
    let y : ℝ := M₀
    let B := Real.log (y + 1) / Real.log y +
      Real.log (Real.log ((y + 1) ^ 2)) / Real.log y * ((k : ℝ) / (k + 1))
    let C := (y / (y - 1)) ^ ((1 : ℝ) / (k + 1)) * B ^ ((k : ℝ) / (k + 1))
    (M : ℝ) < (4 : ℝ) ^ ((1 : ℝ) / (k + 1)) *
      ((k + 1) * (x : ℝ) ^ ((1 : ℝ) / (k + 1)) / Real.log x ^ ((k : ℝ) / (k + 1))) * C

/-- **Lower bound for the maximal gleeful chain length.** Let $p_1 = 2, p_2 = 3, \dots$ be the
primes in increasing order. Let $k > 1$, $M_0 \ge 6$, $M \ge M_0$ and $x$ be natural numbers with
$p_1^k + \cdots + p_M^k \le x < p_1^k + \cdots + p_{M+1}^k$. Put $y = M_0$ and
$$D = \frac{y}{y+3} \Big(\frac{\log(y/2)}{\log y + 2 \log\log(y+2)}\Big)^{k/(k+1)},$$
where $\log$ is the natural logarithm. Then
$$\frac{(k+1)\, x^{1/(k+1)}}{(\log x)^{k/(k+1)}} \cdot D \le M.$$

Source: Sara Moore and Jonathan P. Sorenson, *Explicit Bounds and Parallel
Algorithms for Counting Multiply Gleeful Numbers*, INTEGERS 26 (2026), Article A84,
Lemma 2 (`integers-2026-A84-lem-2`), with `D` from Section 2. -/
public theorem_wanted le_maxChainLength (k M₀ M x : ℕ) (hk : 1 < k) (hM₀ : 6 ≤ M₀)
    (hM : M₀ ≤ M) (hx : ∑ i ∈ Finset.range M, Nat.nth Nat.Prime i ^ k ≤ x)
    (hx' : x < ∑ i ∈ Finset.range (M + 1), Nat.nth Nat.Prime i ^ k) :
    let y : ℝ := M₀
    let D := (y / (y + 3)) *
      (Real.log (y / 2) / (Real.log y + 2 * Real.log (Real.log (y + 2)))) ^
        ((k : ℝ) / (k + 1))
    (k + 1) * (x : ℝ) ^ ((1 : ℝ) / (k + 1)) / Real.log x ^ ((k : ℝ) / (k + 1)) * D ≤ M

/-- **Bounds for the logarithm of the maximal gleeful chain length.** Let
$p_1 = 2, p_2 = 3, \dots$ be the primes in increasing order. Let $k > 1$, $M_0 \ge 6$, $M \ge M_0$
and $x$ be natural numbers with $p_1^k + \cdots + p_M^k \le x < p_1^k + \cdots + p_{M+1}^k$.
Put $y = M_0$, let $\log$ be the natural logarithm, and set
$$A = \frac{\log(y/2)}{\log y},$$
$$B = \frac{\log(y+1)}{\log y} + \frac{\log\log((y+1)^2)}{\log y} \cdot \frac{k}{k+1}.$$
Then
$$\frac{\log x}{k+1} \cdot \frac{1}{B} \le \log M < \frac{\log x}{k+1} \cdot \frac{1}{A}.$$

Source: Sara Moore and Jonathan P. Sorenson, *Explicit Bounds and Parallel
Algorithms for Counting Multiply Gleeful Numbers*, INTEGERS 26 (2026), Article A84,
Lemma 3 (`integers-2026-A84-lem-3`), with `A`, `B` from Section 2. -/
public theorem_wanted log_maxChainLength_bounds (k M₀ M x : ℕ) (hk : 1 < k) (hM₀ : 6 ≤ M₀)
    (hM : M₀ ≤ M) (hx : ∑ i ∈ Finset.range M, Nat.nth Nat.Prime i ^ k ≤ x)
    (hx' : x < ∑ i ∈ Finset.range (M + 1), Nat.nth Nat.Prime i ^ k) :
    let y : ℝ := M₀
    let A := Real.log (y / 2) / Real.log y
    let B := Real.log (y + 1) / Real.log y +
      Real.log (Real.log ((y + 1) ^ 2)) / Real.log y * ((k : ℝ) / (k + 1))
    Real.log M < Real.log x / (k + 1) * (1 / A) ∧
      Real.log x / (k + 1) * (1 / B) ≤ Real.log M

/-- **Upper bound for the number of gleeful representations.** Let $p_1 = 2, p_2 = 3, \dots$ be
the primes in increasing order, and for natural numbers $k$ and $x$ let $s_k(x)$ be the number
of pairs $(n, m)$ of natural numbers with $m \ge 1$ and $p_{n+1}^k + \cdots + p_{n+m}^k \le x$.
Let $k > 1$, $M_0 \ge 6$ and $x$ be natural numbers with $p_1^k + \cdots + p_{M_0}^k \le x$. Put
$y = M_0$, let $\log$ be the natural logarithm, and set
$$A = \frac{\log(y/2)}{\log y},$$
$$B = \frac{\log(y+1)}{\log y} + \frac{\log\log((y+1)^2)}{\log y} \cdot \frac{k}{k+1},$$
$$C = \Big(\frac{y}{y-1}\Big)^{1/(k+1)} B^{k/(k+1)}, \qquad E = 1 + \frac{1}{(k+1)A - 1},$$
$$F = \Big(\frac{y+1}{y}\Big)^{(k-1)/k} 4^{(k-1)/(k(k+1))} C^{(k-1)/k} E,$$
$U = 1.25506\,F$ and $c_k = \frac{k^2}{k-1} (k+1)^{(k-1)/k}$. Then
$$s_k(x) \le c_k \cdot \frac{x^{2/(k+1)}}{(\log x)^{2k/(k+1)}} \cdot U.$$

The paper prints the exponent of $\log x$ as $k/(k+1)$; its proof ends with $2k/(k+1)$, which
is stated here and implies the printed bound because $\log x \ge 1$.

Source: Sara Moore and Jonathan P. Sorenson, *Explicit Bounds and Parallel
Algorithms for Counting Multiply Gleeful Numbers*, INTEGERS 26 (2026), Article A84,
Theorem 1 and its proof (`integers-2026-A84-thm-1`), with `c_k, A, B, C, E, F, U`
from Section 2. -/
public theorem_wanted gleefulRepCount_le (k M₀ x : ℕ) (hk : 1 < k) (hM₀ : 6 ≤ M₀)
    (hx : ∑ i ∈ Finset.range M₀, Nat.nth Nat.Prime i ^ k ≤ x) :
    let y : ℝ := M₀
    let κ : ℝ := k
    let A := Real.log (y / 2) / Real.log y
    let B := Real.log (y + 1) / Real.log y +
      Real.log (Real.log ((y + 1) ^ 2)) / Real.log y * (κ / (κ + 1))
    let C := (y / (y - 1)) ^ (1 / (κ + 1)) * B ^ (κ / (κ + 1))
    let E := 1 + 1 / ((κ + 1) * A - 1)
    let F := ((y + 1) / y) ^ ((κ - 1) / κ) * (4 : ℝ) ^ ((κ - 1) / (κ * (κ + 1))) *
      C ^ ((κ - 1) / κ) * E
    let U := 1.25506 * F
    let c := κ ^ 2 / (κ - 1) * (κ + 1) ^ ((κ - 1) / κ)
    ({q : ℕ × ℕ | 0 < q.2 ∧
        ∑ i ∈ Finset.range q.2, Nat.nth Nat.Prime (q.1 + i) ^ k ≤ x}.ncard : ℝ) ≤
      c * ((x : ℝ) ^ (2 / (κ + 1)) / Real.log x ^ (2 * κ / (κ + 1))) * U

/-- **Lower bound for the number of gleeful representations.** Let $p_1 = 2, p_2 = 3, \dots$ be
the primes in increasing order, and for natural numbers $k$ and $x$ let $s_k(x)$ be the number
of pairs $(n, m)$ of natural numbers with $m \ge 1$ and $p_{n+1}^k + \cdots + p_{n+m}^k \le x$.
Let $k > 1$, $M_0 \ge 6$ and $x$ be natural numbers with $p_1^k + \cdots + p_{M_0}^k \le x$. Put
$y = M_0$, let $\log$ be the natural logarithm, and set
$$D = \frac{y}{y+3} \Big(\frac{\log(y/2)}{\log y + 2 \log\log(y+2)}\Big)^{k/(k+1)}$$
and $L = \frac{y-1}{y} D^2$. Then
$$\frac{(k+1)^2}{2} \cdot \frac{x^{2/(k+1)}}{(\log x)^{2k/(k+1)}} \cdot L \le s_k(x).$$

The paper prints the exponent of $\log x$ as $k/(k+1)$; its proof gives $2k/(k+1)$, which is
stated here. The printed form contradicts the upper bound for $s_k(x)$ for large $x$.

Source: Sara Moore and Jonathan P. Sorenson, *Explicit Bounds and Parallel
Algorithms for Counting Multiply Gleeful Numbers*, INTEGERS 26 (2026), Article A84,
Theorem 2 and its proof (`integers-2026-A84-thm-2`), with `D`, `L` from Section 2. -/
public theorem_wanted le_gleefulRepCount (k M₀ x : ℕ) (hk : 1 < k) (hM₀ : 6 ≤ M₀)
    (hx : ∑ i ∈ Finset.range M₀, Nat.nth Nat.Prime i ^ k ≤ x) :
    let y : ℝ := M₀
    let κ : ℝ := k
    let D := (y / (y + 3)) *
      (Real.log (y / 2) / (Real.log y + 2 * Real.log (Real.log (y + 2)))) ^ (κ / (κ + 1))
    let L := (y - 1) / y * D ^ 2
    (κ + 1) ^ 2 / 2 * ((x : ℝ) ^ (2 / (κ + 1)) / Real.log x ^ (2 * κ / (κ + 1))) * L ≤
      ({q : ℕ × ℕ | 0 < q.2 ∧
        ∑ i ∈ Finset.range q.2, Nat.nth Nat.Prime (q.1 + i) ^ k ≤ x}.ncard : ℝ)

end

end MetaMathlibExt
