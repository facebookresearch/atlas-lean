/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Smooth approximants of divisor functions and `π(n)` (statements)

Statement-only targets from Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula
for π(n) with the Divisor Counting Function*. The paper approximates the divisibility indicator
`[k | n]` by `exp(-n k A(k, n) sin²(nπ/k))`, where `A(k, n) sin²(nπ/k) ≥ 1` whenever `k ∤ n`.
The extraction drops the accent that distinguishes each approximant from the exact function;
the approximant is always the quantity being defined. `τ(n) = n.divisors.card`,
`σ(n) = ∑_{d ∣ n} d`, `π(n) = Nat.primeCounting n`. The paper's `A : ℕ × ℕ → ℝ⁺` is a
function `ℕ → ℕ → ℝ`; its positivity is not needed and not assumed.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset

@[expose] public section

/-- Lemma 1: if `A(k, n) sin²(nπ/k) ≥ 1` whenever `k ∤ n`, then for `1 ≤ k ≤ n` the
approximant `exp(-n k A(k, n) sin²(nπ/k))` of `[k | n]` satisfies
`|exp(-n k A(k, n) sin²(nπ/k)) - [k | n]| ≤ e^{-nk}` (absolute value as the bound is meant
two-sided; the difference is `0` when `k ∣ n` and in `(0, e^{-nk}]` otherwise).

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 1 (`integers-2026-A46-lem-1`). -/
public theorem_wanted abs_exp_approx_sub_dvd_indicator_le (A : ℕ → ℕ → ℝ)
    (hA : ∀ k n, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ A k n * Real.sin (n * Real.pi / k) ^ 2)
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    |Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2)) - (if k ∣ n then 1 else 0)| ≤
      Real.exp (-(n * k : ℝ))

/-- Lemma 2: with `A` as in Lemma 1, `τ̃(n) = ∑_{k=1}^{n} exp(-n k A(k, n) sin²(nπ/k))`
satisfies `τ̃(n) = τ(n) + O(1/(eⁿ - 1))` as `n → ∞`.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 2 (`integers-2026-A46-lem-2`). -/
public theorem_wanted divisorCountApprox_sub_isBigO (A : ℕ → ℕ → ℝ)
    (hA : ∀ k n, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ A k n * Real.sin (n * Real.pi / k) ^ 2) :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2)) -
        (n.divisors.card : ℝ)) =O[atTop] fun n : ℕ => 1 / (Real.exp n - 1)

/-- Lemma 3: `π₀(n) = ∑_{m=2}^{n} exp(-m (τ(m) - 2))` satisfies
`π₀(n) - π(n) < 1/(e³ (e - 1))` for all `n ≥ 2`.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 3 (`integers-2026-A46-lem-3`). -/
public theorem_wanted primeCountingApprox_sub_lt (n : ℕ) (hn : 2 ≤ n) :
    ∑ m ∈ Icc 2 n, Real.exp (-(m * ((m.divisors.card : ℝ) - 2))) - Nat.primeCounting n <
      1 / (Real.exp 3 * (Real.exp 1 - 1))

/-- Lemma 4: `A(k, n) = π² k² / 2` satisfies `A(k, n) sin²(nπ/k) ≥ 1` for all positive integers
`k, n` with `k ∤ n`.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 4 (`integers-2026-A46-lem-4`). -/
public theorem_wanted one_le_pi_sq_mul_sq_div_two_mul_sin_sq (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) (hkn : ¬ k ∣ n) :
    1 ≤ Real.pi ^ 2 * k ^ 2 / 2 * Real.sin (n * Real.pi / k) ^ 2

/-- Theorem 1: `τ̃(k) = ∑_{j=1}^{k} exp(-(π²/2) k j³ sin²(kπ/j))` (the paper's (1), i.e.
Lemma 2 with `A(j, k) = π² j²/2`) satisfies `τ̃(k) = τ(k) + O(1/(eᵏ - 1))` as `k → ∞`.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Theorem 1 (`integers-2026-A46-thm-1`). -/
public theorem_wanted divisorCountApprox_one_sub_isBigO :
    (fun k : ℕ => ∑ j ∈ Icc 1 k,
        Real.exp (-(Real.pi ^ 2 / 2 * k * j ^ 3 * Real.sin (k * Real.pi / j) ^ 2)) -
        (k.divisors.card : ℝ)) =O[atTop] fun k : ℕ => 1 / (Real.exp k - 1)

/-- Theorem 2: with `τ̃` from (1), `π̃(n) = ∑_{k=2}^{n} e^{-k(τ̃(k) - 2)}` satisfies
`|π̃(n) - π(n)| < 0.7129749140934` for all `n ≥ 2` (the record's extraction drops the absolute
value bars; the constant is `0.684 + 1/(e³(e - 1))`, the sum of the one-sided bounds, as the
two-sided reading requires).

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Theorem 2 (`integers-2026-A46-thm-2`). -/
public theorem_wanted primeCountingApprox_abs_sub_lt (n : ℕ) (hn : 2 ≤ n) :
    let τ' : ℕ → ℝ := fun k => ∑ j ∈ Icc 1 k,
      Real.exp (-(Real.pi ^ 2 / 2 * k * j ^ 3 * Real.sin (k * Real.pi / j) ^ 2))
    |∑ k ∈ Icc 2 n, Real.exp (-(k * (τ' k - 2))) - Nat.primeCounting n| < 0.7129749140934

/-- Theorem 3: with `A` as in Lemma 1, `σ̃(n) = ∑_{k=1}^{n} k exp(-n k A(k, n) sin²(nπ/k))`
satisfies `σ̃(n) - σ(n) < n/(eⁿ - 1)` for all `n ≥ 1`.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Theorem 3 (`integers-2026-A46-thm-3`). -/
public theorem_wanted divisorSumApprox_sub_lt (A : ℕ → ℕ → ℝ)
    (hA : ∀ k n, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ A k n * Real.sin (n * Real.pi / k) ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, k * Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2)) -
        ∑ d ∈ n.divisors, (d : ℝ) < n / (Real.exp n - 1)

end

end MetaMathlibExt
