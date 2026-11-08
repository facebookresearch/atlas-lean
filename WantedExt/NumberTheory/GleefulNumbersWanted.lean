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

/-- **Lemma 1.** If `k > 1` and `M = M(x, k) ≥ M₀ ≥ 6`, then
`M < 4^{1/(k+1)} (k+1) x^{1/(k+1)} / (log x)^{k/(k+1)} · C(M₀, k)`.

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

/-- **Lemma 2.** If `k > 1` and `M = M(x, k) ≥ M₀ ≥ 6`, then
`M ≥ (k+1) x^{1/(k+1)} / (log x)^{k/(k+1)} · D(M₀, k)`.

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

/-- **Lemma 3.** If `k > 1` and `M = M(x, k) ≥ M₀ ≥ 6`, then
`log M < log x / (k+1) · 1 / A(M₀)` and `log M ≥ log x / (k+1) · 1 / B(M₀, k)`.

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

/-- **Theorem 1.** If `k > 1` and `M(x, k) ≥ M₀ ≥ 6`, then
`s_k(x) ≤ c_k · x^{2/(k+1)} / (log x)^{2k/(k+1)} · U(M₀, k)`.

The printed exponent of `log x` is `k/(k+1)`; the paper's proof ends with
`2k/(k+1)`, which is stated here and implies the printed bound since `log x ≥ 1`.

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

/-- **Theorem 2.** If `k > 1` and `M(x, k) ≥ M₀ ≥ 6`, then
`s_k(x) ≥ (k+1)^2 / 2 · x^{2/(k+1)} / (log x)^{2k/(k+1)} · L(M₀, k)`.

The printed exponent of `log x` is `k/(k+1)`; the paper's proof (from
`s_k(x) ≥ M(M-1)/2` and Lemma 2) gives `2k/(k+1)`, stated here. The printed form
contradicts Theorem 1 for large `x`.

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
