/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Sums of powers of consecutive primes (statements)

Statement-only targets from Cathal O'Sullivan, Jonathan P. Sorenson, and Aryn Stahl,
*Algorithms and Bounds on the Sums of Powers of Consecutive Primes*. With
`p_{i+1} = Nat.nth Nat.Prime i`:
- `s_{k,m}(x) = #{n ≤ x : n = p_{ℓ+1}^k + ⋯ + p_{ℓ+m}^k for some ℓ ≥ 0}`;
- `s_k(x) = ∑_{m ≥ 1} s_{k,m}(x)`; since the `m`-term sum is strictly increasing in `ℓ`,
  this is the number of pairs `(ℓ, m)`, `m ≥ 1`, with `p_{ℓ+1}^k + ⋯ + p_{ℓ+m}^k ≤ x`;
- `M(x, k)`, the length of the longest sum of `k`-th powers of consecutive primes `≤ x`, is the
  largest `m` with `p_1^k + ⋯ + p_m^k ≤ x`.
All are written inline for natural `x` (the counts only depend on `⌊x⌋`). Since
`p_{ℓ+1} > ℓ + 1` and every `k`-th power of a prime is at least `4`, a sum `≤ x` has `ℓ < x` and
`m ≤ x`, so the finite ranges used below lose nothing.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset

@[expose] public section

/-- Lemma 1: for `k > 1` and `m > 0`, `s_{k,m}(x) ≤ π((x/m)^{1/k})`.

Source: Cathal O'Sullivan, Jonathan P. Sorenson, and Aryn Stahl, *Algorithms and Bounds on the
Sums of Powers of Consecutive Primes*, INTEGERS 24 (2024), Article A4, Lemma 1 (quoted from
[6]) (`integers-2024-A4-lem-1`). -/
public theorem_wanted card_consecutivePrimePowerSums_length_le (k m x : ℕ) (hk : 1 < k)
    (hm : 0 < m) :
    {n : ℕ | n ≤ x ∧ ∃ l, n = ∑ i ∈ range m, Nat.nth Nat.Prime (l + i) ^ k}.ncard ≤
      Nat.primeCounting ⌊((x : ℝ) / m) ^ ((1 : ℝ) / k)⌋₊

/-- Lemma 2: for `k > 1`, `M(x, k) ∼ (k + 1) x^{1/(k+1)} / (log x)^{k/(k+1)}` as `x → ∞`.

Source: Cathal O'Sullivan, Jonathan P. Sorenson, and Aryn Stahl, *Algorithms and Bounds on the
Sums of Powers of Consecutive Primes*, INTEGERS 24 (2024), Article A4, Lemma 2
(`integers-2024-A4-lem-2`). -/
public theorem_wanted maxConsecutivePrimePowerSumLength_isEquivalent (k : ℕ) (hk : 1 < k) :
    (fun x : ℕ =>
        (Nat.findGreatest (fun m => ∑ i ∈ range m, Nat.nth Nat.Prime i ^ k ≤ x) x : ℝ)) ~[atTop]
      fun x : ℕ => (k + 1) * (x : ℝ) ^ ((1 : ℝ) / (k + 1)) /
        Real.log x ^ ((k : ℝ) / (k + 1))

/-- Theorem 1: for `k > 1`,
`s_k(x) ≤ (1 + o(1)) c_k x^{2/(k+1)} / (log x)^{2k/(k+1)}` with
`c_k = (k²/(k - 1)) (k + 1)^{1 - 1/k}`; the `1 + o(1)` is stated as: for every `ε > 0`, the bound
with factor `1 + ε` holds for all sufficiently large `x`.

Source: Cathal O'Sullivan, Jonathan P. Sorenson, and Aryn Stahl, *Algorithms and Bounds on the
Sums of Powers of Consecutive Primes*, INTEGERS 24 (2024), Article A4, Theorem 1
(`integers-2024-A4-thm-1`). -/
public theorem_wanted card_consecutivePrimePowerSums_le (k : ℕ) (hk : 1 < k) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (((range x ×ˢ Icc 1 x).filter (fun lm =>
          ∑ i ∈ range lm.2, Nat.nth Nat.Prime (lm.1 + i) ^ k ≤ x)).card : ℝ) ≤
        (1 + ε) * ((k ^ 2 / (k - 1) : ℝ) * ((k : ℝ) + 1) ^ (1 - (1 : ℝ) / k)) *
          ((x : ℝ) ^ ((2 : ℝ) / (k + 1)) / Real.log x ^ ((2 * k : ℝ) / (k + 1)))

/-- Theorem 2: for `k > 1`,
`s_k(x) ≥ M²/2 ≥ (1 + o(1)) (k + 1)² x^{2/(k+1)} / (2 (log x)^{2k/(k+1)})` with
`M = M(x, k)`. The extraction lost the square on `M` (superscripts are flattened throughout the
record). The `1 + o(1)` is stated as: for every `ε > 0`, the bound with factor `1 - ε` holds
for all sufficiently large `x`.

Source: Cathal O'Sullivan, Jonathan P. Sorenson, and Aryn Stahl, *Algorithms and Bounds on the
Sums of Powers of Consecutive Primes*, INTEGERS 24 (2024), Article A4, Theorem 2
(`integers-2024-A4-thm-2`). -/
public theorem_wanted card_consecutivePrimePowerSums_ge (k : ℕ) (hk : 1 < k) :
    let s : ℕ → ℝ := fun x =>
      (((range x ×ˢ Icc 1 x).filter (fun lm =>
          ∑ i ∈ range lm.2, Nat.nth Nat.Prime (lm.1 + i) ^ k ≤ x)).card : ℝ)
    let M : ℕ → ℝ := fun x =>
      (Nat.findGreatest (fun m => ∑ i ∈ range m, Nat.nth Nat.Prime i ^ k ≤ x) x : ℝ)
    (∀ x : ℕ, M x ^ 2 / 2 ≤ s x) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
        (1 - ε) * (((k : ℝ) + 1) ^ 2 * (x : ℝ) ^ ((2 : ℝ) / (k + 1)) /
          (2 * Real.log x ^ ((2 * k : ℝ) / (k + 1)))) ≤ M x ^ 2 / 2

end

end MetaMathlibExt
