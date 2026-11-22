/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting

/-! # Explicit prime bounds from the refinements of Mandl's inequality

Statement-only requests for the explicit lemmas, propositions, corollaries and Theorem 1 of
Zhang and Xiong. The source's one-indexed `pₙ` is `Nat.nth Nat.Prime (n - 1)` and `π(x)` is
`Nat.primeCounting ⌊x⌋₊`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Rosser–Schoenfeld lower bound quoted as Lemma 2: `x / log x < π(x)` for every real
`x ≥ 17`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 2 (`integers-2025-A58-lem-2`). -/
public theorem_wanted primeCounting_gt_div_log_of_seventeen_le (x : ℝ) (hx : 17 ≤ x) :
    x / Real.log x < (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- Consequence (2) of Lemma 2: `pₙ < n log pₙ` for every `n ≥ 7` (one-indexed `pₙ`, so
`pₙ = Nat.nth Nat.Prime (n - 1)`).

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 2, inequality (2) (`integers-2025-A58-lem-2`). -/
public theorem_wanted nthPrime_lt_mul_log_nthPrime (n : ℕ) (hn : 7 ≤ n) :
    (Nat.nth Nat.Prime (n - 1) : ℝ) < n * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ)

/-- Dusart upper bound quoted in Lemma 3: `π(x) < x / (log x - 1.1)` for every real
`x ≥ 60184`.
The companion lower bound `π(x) > x / (log x - 1)` for `x ≥ 5393` is
`MetaMathlibExt.dusart_pi_lower_shifted_log`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 3 (`integers-2025-A58-lem-3`). -/
public theorem_wanted primeCounting_lt_div_log_sub_eleven_tenths (x : ℝ) (hx : 60184 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / (Real.log x - 1.1)

/-- Consequence (4) of Lemma 3: `pₙ < n (log pₙ - 1)` for every `n ≥ 711 = π(5393)`
(one-indexed `pₙ`). Consequence (3) is omitted: it fails at `n = 6076`, where `p₆₀₇₆ = 60169` and
`6076 (log 60169 - 1.1) ≈ 60182.2`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 3, inequality (4) (`integers-2025-A58-lem-3`). -/
public theorem_wanted nthPrime_lt_mul_log_nthPrime_sub_one (n : ℕ) (hn : 711 ≤ n) :
    (Nat.nth Nat.Prime (n - 1) : ℝ) < n * (Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) - 1)

/-- Lower bound quoted as Lemma 4: `π(x) > x / (log x - 1 - 1 / log x)` for every real
`x ≥ 468049`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 4 (`integers-2025-A58-lem-4`). -/
public theorem_wanted primeCounting_gt_div_log_sub_one_sub_inv_log (x : ℝ) (hx : 468049 ≤ x) :
    x / (Real.log x - 1 - 1 / Real.log x) < (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- Consequence (5) of Lemma 4: `pₙ < n (log pₙ - 1 - 1 / log pₙ)` for every `n ≥ 39071 =
π(468049)` (one-indexed `pₙ`).

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 4, inequality (5) (`integers-2025-A58-lem-4`). -/
public theorem_wanted nthPrime_lt_mul_log_nthPrime_sub_one_sub_inv_log (n : ℕ) (hn : 39071 ≤ n) :
    (Nat.nth Nat.Prime (n - 1) : ℝ) <
      n * (Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) - 1 -
        1 / Real.log (Nat.nth Nat.Prime (n - 1) : ℝ))

/-- Lemma 6, inequality (15): `log n ≥ 0.914 log pₙ` for every `n ≥ 234057667276344608`
(one-indexed `pₙ`).

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 6, inequality (15) (`integers-2025-A58-lem-6`). -/
public theorem_wanted mul_log_nthPrime_le_log (n : ℕ) (hn : 234057667276344608 ≤ n) :
    0.914 * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) ≤ Real.log n

/-- Proposition 1: for every `n ≥ 1`, with one-indexed `pₙ`,
`937.5 pₙ² log pₙ + 5674.5 pₙ² > 118.676119576 n² log³ pₙ + 709.7856 n pₙ log² pₙ`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Proposition 1 (`integers-2025-A58-prop-1`). -/
public theorem_wanted nthPrime_sq_log_bound (n : ℕ) (hn : 1 ≤ n) :
    118.676119576 * (n : ℝ) ^ 2 * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 3 +
        709.7856 * n * (Nat.nth Nat.Prime (n - 1) : ℝ) *
          Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 2 <
      937.5 * (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 2 * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) +
        5674.5 * (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 2

/-- Proposition 3, inequality (25): for every integer `n ≥ 2`, with `L = log n`,
`4.151332 (log L - 2) / L + 3.151332 (log L - 1) / L + 3.151332 (log L - 2) / L² ≤ 1`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Proposition 3, inequality (25) (`integers-2025-A58-prop-3`). -/
public theorem_wanted loglog_ratio_sum_le_one (n : ℕ) (hn : 2 ≤ n) :
    4.151332 * (Real.log (Real.log n) - 2) / Real.log n +
        3.151332 * (Real.log (Real.log n) - 1) / Real.log n +
        3.151332 * (Real.log (Real.log n) - 2) / Real.log n ^ 2 ≤ 1

/-- Corollary 1, inequalities (6)-(9): with one-indexed `pₙ` and `L = log pₙ`,
`pₙ > n (L - 1 - 1.109 / L)` for `n ≥ 2621506158680`,
`pₙ > n (L - 1 - 1 / L - 3.48 / L²)` for `n ≥ 4605081012945`,
`pₙ > n (L - 1 - 1 / L - 3.024334 / L² - 14.893 / L³)` for `n ≥ 4514634967572`, and
`pₙ > n (L - 1 - 1 / L - 3.024334 / L² - 12.975666 / L³ - 79.962 / L⁴)` for `n ≥ 8`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Corollary 1 (`integers-2025-A58-cor-1`). -/
public theorem_wanted nthPrime_gt_mul_log_sub_corollary_one :
    (∀ n : ℕ, 2621506158680 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      n * (Real.log p - 1 - 1.109 / Real.log p) < p) ∧
    (∀ n : ℕ, 4605081012945 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      n * (Real.log p - 1 - 1 / Real.log p - 3.48 / Real.log p ^ 2) < p) ∧
    (∀ n : ℕ, 4514634967572 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      n * (Real.log p - 1 - 1 / Real.log p - 3.024334 / Real.log p ^ 2 -
        14.893 / Real.log p ^ 3) < p) ∧
    (∀ n : ℕ, 8 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      n * (Real.log p - 1 - 1 / Real.log p - 3.024334 / Real.log p ^ 2 -
        12.975666 / Real.log p ^ 3 - 79.962 / Real.log p ^ 4) < p)

/-- Corollary 2, inequalities (10)-(14): with one-indexed `pₙ` and `L = log pₙ`,
`pₙ < n (L - 1 - 1 / L - 2.975666 / L²)` for `n ≥ 3278841`, and the bounds obtained by further
subtracting `13.024334 / L³` (`n ≥ 355193892`), `70.951332 / L⁴` (`n ≥ 6226419706`),
`460.634397856444 / L⁵` (`n ≥ 38900733192`) and `3444.031844143556 / L⁶` (`n ≥ 64497259289`).

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Corollary 2 (`integers-2025-A58-cor-2`). -/
public theorem_wanted nthPrime_lt_mul_log_sub_corollary_two :
    (∀ n : ℕ, 3278841 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      p < n * (Real.log p - 1 - 1 / Real.log p - 2.975666 / Real.log p ^ 2)) ∧
    (∀ n : ℕ, 355193892 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      p < n * (Real.log p - 1 - 1 / Real.log p - 2.975666 / Real.log p ^ 2 -
        13.024334 / Real.log p ^ 3)) ∧
    (∀ n : ℕ, 6226419706 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      p < n * (Real.log p - 1 - 1 / Real.log p - 2.975666 / Real.log p ^ 2 -
        13.024334 / Real.log p ^ 3 - 70.951332 / Real.log p ^ 4)) ∧
    (∀ n : ℕ, 38900733192 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      p < n * (Real.log p - 1 - 1 / Real.log p - 2.975666 / Real.log p ^ 2 -
        13.024334 / Real.log p ^ 3 - 70.951332 / Real.log p ^ 4 -
        460.634397856444 / Real.log p ^ 5)) ∧
    (∀ n : ℕ, 64497259289 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      p < n * (Real.log p - 1 - 1 / Real.log p - 2.975666 / Real.log p ^ 2 -
        13.024334 / Real.log p ^ 3 - 70.951332 / Real.log p ^ 4 -
        460.634397856444 / Real.log p ^ 5 - 3444.031844143556 / Real.log p ^ 6))

/-- Lemma 8 (quoted from the literature):
`log pₙ ≥ log n + log log n + log(1 + (log log n - 1) / log n)` (one-indexed `pₙ`). The paper
says "for all positive integers `n`"; the right side is undefined at `n = 1` (`log log 1`) and
at `n = 2` (the last logarithm's argument is `≈ -0.9715`), so `n ≥ 3`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 8, inequality (17) (`integers-2025-A58-lem-8`). -/
public theorem_wanted log_nthPrime_ge_log_add_loglog (n : ℕ) (hn : 3 ≤ n) :
    Real.log n + Real.log (Real.log n) +
        Real.log (1 + (Real.log (Real.log n) - 1) / Real.log n) ≤
      Real.log (Nat.nth Nat.Prime (n - 1) : ℝ)

/-- Lemma 9 (quoted from the literature): with one-indexed `pₙ`, `L = log pₙ` and
`S = n pₙ - ∑_{k ≤ n} p_k`, inequality (18):
`S ≥ pₙ² (1/(2L) + 3/(4L²) + 7/(4L³) + 44.4/(8L⁴) + 92.1/(4L⁵) + 937.5/(8L⁶) + 5674.5/(8L⁷)
+ 79789.5/(16L⁸))` for `n ≥ 440200309`, and inequality (19):
`S ≤ pₙ² (1/(2L) + 3/(4L²) + 7/(4L³) + 45.6/(8L⁴) + 93.9/(4L⁵) + 952.5/(8L⁶) + 5755.5/(8L⁷)
+ 116371/(16L⁸))` for every `n ≥ 1`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 9 (`integers-2025-A58-lem-9`). -/
public theorem_wanted mul_nthPrime_sub_sum_primes_bounds :
    (∀ n : ℕ, 440200309 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      let L : ℝ := Real.log p
      p ^ 2 / (2 * L) + 3 * p ^ 2 / (4 * L ^ 2) + 7 * p ^ 2 / (4 * L ^ 3) +
          44.4 * p ^ 2 / (8 * L ^ 4) + 92.1 * p ^ 2 / (4 * L ^ 5) + 937.5 * p ^ 2 / (8 * L ^ 6) +
          5674.5 * p ^ 2 / (8 * L ^ 7) + 79789.5 * p ^ 2 / (16 * L ^ 8) ≤
        n * p - ∑ k ∈ Finset.range n, (Nat.nth Nat.Prime k : ℝ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      let L : ℝ := Real.log p
      n * p - ∑ k ∈ Finset.range n, (Nat.nth Nat.Prime k : ℝ) ≤
        p ^ 2 / (2 * L) + 3 * p ^ 2 / (4 * L ^ 2) + 7 * p ^ 2 / (4 * L ^ 3) +
          45.6 * p ^ 2 / (8 * L ^ 4) + 93.9 * p ^ 2 / (4 * L ^ 5) + 952.5 * p ^ 2 / (8 * L ^ 6) +
          5755.5 * p ^ 2 / (8 * L ^ 7) + 116371 * p ^ 2 / (16 * L ^ 8))

/-- Proposition 2: for every `n ≥ 4605081012945`, with one-indexed `pₙ`, `ℓ = log n`,
`L = log pₙ` and `M(n) = n pₙ / 2 - ∑_{k ≤ n} p_k`,
`M(n) > n²/4 + n²/(4ℓ) - n² log ℓ/(4ℓ²) + ω(n) n²/ℓ²`, where
`ω(n) = 3.151332 ℓ²/(4L²) + ℓ²/(4L) + 16.7 ℓ²/(4L³) - ℓ/4 + log ℓ/4`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Proposition 2 (`integers-2025-A58-prop-2`). -/
public theorem_wanted mandl_sum_gt_omega_bound (n : ℕ) (hn : 4605081012945 ≤ n) :
    let p : ℝ := Nat.nth Nat.Prime (n - 1)
    let l : ℝ := Real.log n
    let L : ℝ := Real.log p
    let ω : ℝ := 3.151332 * l ^ 2 / (4 * L ^ 2) + l ^ 2 / (4 * L) + 16.7 * l ^ 2 / (4 * L ^ 3) -
      l / 4 + Real.log l / 4
    (n : ℝ) ^ 2 / 4 + (n : ℝ) ^ 2 / (4 * l) - (n : ℝ) ^ 2 * Real.log l / (4 * l ^ 2) +
        ω * (n : ℝ) ^ 2 / l ^ 2 <
      n * p / 2 - ∑ k ∈ Finset.range n, (Nat.nth Nat.Prime k : ℝ)

/-- Proposition 4: for every `n ≥ 64497259289`, with one-indexed `pₙ`, `ℓ = log n`,
`L = log pₙ` and `M(n) = n pₙ / 2 - ∑_{k ≤ n} p_k`,
`M(n) < n²/4 + n²/(4ℓ) - n² log ℓ/(4ℓ²) + Ω(n) n²/ℓ²`, where
`Ω(n) = ℓ²/(4L) + 3.848668 ℓ²/(4L²) - ℓ/4 + log ℓ/4 + τ(L) ℓ²/(8L⁶)` and
`τ(x) = 34.6x³ + 205.592008x² + 1420.426661948448x + 28890.293784512888`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Proposition 4 (`integers-2025-A58-prop-4`). -/
public theorem_wanted mandl_sum_lt_Omega_bound (n : ℕ) (hn : 64497259289 ≤ n) :
    let p : ℝ := Nat.nth Nat.Prime (n - 1)
    let l : ℝ := Real.log n
    let L : ℝ := Real.log p
    let τ : ℝ := 34.6 * L ^ 3 + 205.592008 * L ^ 2 + 1420.426661948448 * L +
      28890.293784512888
    let Ω : ℝ := l ^ 2 / (4 * L) + 3.848668 * l ^ 2 / (4 * L ^ 2) - l / 4 + Real.log l / 4 +
      τ * l ^ 2 / (8 * L ^ 6)
    n * p / 2 - ∑ k ∈ Finset.range n, (Nat.nth Nat.Prime k : ℝ) <
      (n : ℝ) ^ 2 / 4 + (n : ℝ) ^ 2 / (4 * l) - (n : ℝ) ^ 2 * Real.log l / (4 * l ^ 2) +
        Ω * (n : ℝ) ^ 2 / l ^ 2

/-- Theorem 1: with one-indexed `pₙ`, `M(n) = n pₙ / 2 - ∑_{k ≤ n} p_k` and
`B_η(n) = n²/4 (1 + 1/log n - (log log n - η)/log² n)`, `B_α(n) < M(n)` for
`n ≥ 234057667276344608` and `M(n) < B_β(n)` for `n ≥ 64497259289`, where `α = 3.151332` and
`β = 4.168668`.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Theorem 1 (`integers-2025-A58-thm-1`). -/
public theorem_wanted mandl_sum_between_B_alpha_B_beta :
    let M : ℕ → ℝ := fun n =>
      n * (Nat.nth Nat.Prime (n - 1) : ℝ) / 2 - ∑ k ∈ Finset.range n, (Nat.nth Nat.Prime k : ℝ)
    let B : ℝ → ℕ → ℝ := fun η n =>
      (n : ℝ) ^ 2 / 4 *
        (1 + 1 / Real.log n - (Real.log (Real.log n) - η) / Real.log n ^ 2)
    (∀ n : ℕ, 234057667276344608 ≤ n → B 3.151332 n < M n) ∧
    (∀ n : ℕ, 64497259289 ≤ n → M n < B 4.168668 n)

end

end MetaMathlibExt
