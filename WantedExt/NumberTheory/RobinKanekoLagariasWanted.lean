/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Primorial
public import WantedExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumWanted

namespace MetaMathlibExt

@[expose] public section

open Filter Topology Real

/-- The real extension `H(x) = ∫₀¹ (t^x - 1)/(t - 1) dt` of the harmonic numbers (`H(n) = H_n`).

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Section 3.1 (definition of `H(x)`). -/
noncomputable def harmonicExtension (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (t ^ x - 1) / (t - 1)

/-- `H(0) = 0`.

Source: Assani, Chester, and Paschal, INTEGERS 26 (2026), Article A86, Section 3.1 (definition of
`H(x)`). -/
theorem harmonicExtension_zero : harmonicExtension 0 = 0 := by
  simp [harmonicExtension]

/-- Bridge: `H(n) = H_n` for natural `n`.

Source: Assani, Chester, and Paschal, INTEGERS 26 (2026), Article A86, Section 3.1 ("`H(n) = H_n`
for all `n ∈ ℕ`"). -/
public theorem_wanted harmonicExtension_natCast (n : ℕ) :
    harmonicExtension n = harmonic n

/-- Rosser–Schoenfeld and Dusart bounds for the `k`-th prime `p_k` (`p_1 = 2`): for `k ≥ 6`,
`k(log k + log log k - 1) < p_k < k(log k + log log k)`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 1, equation (3)
(`integers-2026-A86-thm-1`). -/
public theorem_wanted nth_prime_bounds (k : ℕ) (hk : 6 ≤ k) :
    (k : ℝ) * (log k + log (log k) - 1) < Nat.nth Nat.Prime (k - 1) ∧
      (Nat.nth Nat.Prime (k - 1) : ℝ) < k * (log k + log (log k))

/-- For `k ≥ 99` and `1 ≤ j ≤ k + 1`, with `m = p_{k+1}# / p_j`,
`log log m > log((k+1)(log(k+1) + log log(k+1) - 1) log 2.51 - log p_j)`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 4 (`integers-2026-A86-lem-4`).
-/
public theorem_wanted log_log_primorial_div_prime_gt (k j : ℕ) (hk : 99 ≤ k) (hj : 1 ≤ j)
    (hjk : j ≤ k + 1) :
    log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1) * log (251 / 100) -
        log (Nat.nth Nat.Prime (j - 1))) <
      log (log ((primorial (Nat.nth Nat.Prime k) : ℝ) / Nat.nth Nat.Prime (j - 1)))

/-- Robin's inequality `σ(n) < e^γ n log log n` holds for every `n > 5040` not divisible by one
of `p_1, p_2, p_3 = 2, 3, 5`. (The paper prints Robin's inequality as `σ(n) < e^γ log log n`,
dropping the factor `n`; the standard form, which the paper uses in Section 2, is formalized.)

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 4 (`integers-2026-A86-thm-4`).
-/
public theorem_wanted robin_inequality_of_not_dvd (p : ℕ) (hp : p ∈ ({2, 3, 5} : Finset ℕ))
    (n : ℕ) (hn : 5040 < n) (hdvd : ¬ p ∣ n) :
    (ArithmeticFunction.sigma 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n)

/-- For `k ≥ 1` and odd `n > b(k) = e^{e^{√(2.51(2^{k+1} - 1)/e^γ)}} / 2^k`, Robin's inequality
holds for `2^k n`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 5, equation (12)
(`integers-2026-A86-thm-5`). -/
public theorem_wanted robin_inequality_two_pow_mul_odd (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : Odd n)
    (hb : exp (exp (√((251 / 100 : ℝ) * (2 ^ (k + 1) - 1) / exp eulerMascheroniConstant))) /
      2 ^ k < n) :
    (ArithmeticFunction.sigma 1 (2 ^ k * n) : ℝ) <
      exp eulerMascheroniConstant * (2 ^ k * n : ℕ) * log (log (2 ^ k * n : ℕ))

/-- Robin's inequality holds for `2n` for every odd `n ≥ 620`, and for every primorial
`m# > 30`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Corollary 2
(`integers-2026-A86-cor-2`). -/
public theorem_wanted robin_inequality_two_mul_odd_and_primorial :
    (∀ n : ℕ, Odd n → 620 ≤ n →
      (ArithmeticFunction.sigma 1 (2 * n) : ℝ) <
        exp eulerMascheroniConstant * (2 * n : ℕ) * log (log (2 * n : ℕ))) ∧
    ∀ m : ℕ, 30 < primorial m →
      (ArithmeticFunction.sigma 1 (primorial m) : ℝ) <
        exp eulerMascheroniConstant * primorial m * log (log (primorial m))

/-- For `k ≥ 1` with `2^k b̃(k) = e^{e^{(0.0168(2^{k+1} - 1)/e^γ)^{1/3}}} < C = 10^{10^{13.11485}}`,
Robin's inequality holds for every `2^k n > 5040` with `n` odd; in particular it holds for every
`21`-free `n > 5040`. The paper omits `> 5040`; as printed the claims fail at `2 · 3 = 6` and at
the `21`-free `n = 12`, and its proof treats exactly the range `2^k n > 5041`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 7 (`integers-2026-A86-thm-7`).
-/
public theorem_wanted robin_inequality_two_pow_mul_odd_and_twentyOne_free :
    (∀ k : ℕ, 1 ≤ k →
      exp (exp (((168 / 10000 : ℝ) * (2 ^ (k + 1) - 1) / exp eulerMascheroniConstant) ^
        (1 / 3 : ℝ))) < (10 : ℝ) ^ ((10 : ℝ) ^ (1311485 / 100000 : ℝ)) →
      ∀ n : ℕ, Odd n → 5040 < 2 ^ k * n →
        (ArithmeticFunction.sigma 1 (2 ^ k * n) : ℝ) <
          exp eulerMascheroniConstant * (2 ^ k * n : ℕ) * log (log (2 ^ k * n : ℕ))) ∧
    ∀ n : ℕ, 5040 < n → (∀ p : ℕ, p.Prime → ¬ p ^ 21 ∣ n) →
      (ArithmeticFunction.sigma 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n)

/-- The set of `n` satisfying Robin's inequality `σ(n) < e^γ n log log n` has natural density `1`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 8 (`integers-2026-A86-thm-8`).
-/
public theorem_wanted robin_inequality_density_one :
    Tendsto (fun N : ℕ => ((Finset.Icc 1 N).filter fun n : ℕ =>
        (ArithmeticFunction.sigma 1 n : ℝ) <
          exp eulerMascheroniConstant * n * log (log n)).card / (N : ℝ)) atTop (𝓝 1)

/-- For `x ≥ 1`, `H(x) < log x + γ + 1/(2x)`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 6 (`integers-2026-A86-lem-6`).
-/
public theorem_wanted harmonicExtension_lt_log_add (x : ℝ) (hx : 1 ≤ x) :
    harmonicExtension x < log x + eulerMascheroniConstant + 1 / (2 * x)

/-- For `x ≥ 4`, `H(x) < 2 log x / (1 + 6/(π² x))`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 7 (`integers-2026-A86-lem-7`).
-/
public theorem_wanted harmonicExtension_lt_two_log (x : ℝ) (hx : 4 ≤ x) :
    harmonicExtension x < 2 * log x / (1 + 6 / (π ^ 2 * x))

/-- For `n > 1`, `H_{n+1} ≤ n / log n`; for `x ≥ 4`, `log H(x) ≤ x / (2 log x)`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 8 (`integers-2026-A86-lem-8`).
-/
public theorem_wanted harmonic_succ_le_and_log_harmonicExtension_le :
    (∀ n : ℕ, 1 < n → (harmonic (n + 1) : ℝ) ≤ n / log n) ∧
    ∀ x : ℝ, 4 ≤ x → log (harmonicExtension x) ≤ x / (2 * log x)

/-- For `x ≥ 4`, `H(x) log H(x) < x² / (x + 6/π²)`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 9 (`integers-2026-A86-lem-9`).
-/
public theorem_wanted harmonicExtension_mul_log_lt (x : ℝ) (hx : 4 ≤ x) :
    harmonicExtension x * log (harmonicExtension x) < x ^ 2 / (x + 6 / π ^ 2)

/-- For `x ≥ 4`, `H'(x) > H(x) log H(x) / x²`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 10 (`integers-2026-A86-lem-10`).
-/
public theorem_wanted harmonicExtension_mul_log_div_sq_lt_deriv (x : ℝ) (hx : 4 ≤ x) :
    harmonicExtension x * log (harmonicExtension x) / x ^ 2 < deriv harmonicExtension x

/-- `g(x) = exp(H(x)) log H(x) / x` is increasing on `[4, ∞)`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Proposition 2
(`integers-2026-A86-prop-2`). -/
public theorem_wanted exp_harmonicExtension_mul_log_div_monotoneOn :
    MonotoneOn (fun x : ℝ => exp (harmonicExtension x) * log (harmonicExtension x) / x)
      (Set.Ici 4)

/-- The sequence `exp(H_n) log(H_n) / n` (`n ≥ 1`) is monotonically increasing.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Corollary 3
(`integers-2026-A86-cor-3`). -/
public theorem_wanted exp_harmonic_mul_log_div_monotoneOn :
    MonotoneOn (fun n : ℕ => exp (harmonic n : ℝ) * log (harmonic n : ℝ) / n) (Set.Ici 1)

/-- If the Kaneko–Lagarias inequality `σ(n) < exp(H_n) log H_n` (asserted for `n > 60`) fails,
its least counterexample `n₀ > 60` is superabundant: `σ(m)/m < σ(n₀)/n₀` for all `1 ≤ m < n₀`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 9 (`integers-2026-A86-thm-9`).
-/
public theorem_wanted least_kaneko_lagarias_counterexample_superabundant (n₀ : ℕ) (hn₀ : 60 < n₀)
    (hfail : ¬ (ArithmeticFunction.sigma 1 n₀ : ℝ) <
      exp (harmonic n₀ : ℝ) * log (harmonic n₀ : ℝ))
    (hleast : ∀ n : ℕ, 60 < n → n < n₀ →
      (ArithmeticFunction.sigma 1 n : ℝ) < exp (harmonic n : ℝ) * log (harmonic n : ℝ)) :
    ∀ m : ℕ, 1 ≤ m → m < n₀ →
      (ArithmeticFunction.sigma 1 m : ℝ) / m < (ArithmeticFunction.sigma 1 n₀ : ℝ) / n₀

/-- If Robin's inequality `σ(n) < e^γ n log log n` holds for `n`, then so does the
Kaneko–Lagarias inequality `σ(n) < exp(H_n) log H_n`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 10
(`integers-2026-A86-thm-10`). -/
public theorem_wanted kaneko_lagarias_of_robin (n : ℕ)
    (h : (ArithmeticFunction.sigma 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n)) :
    (ArithmeticFunction.sigma 1 n : ℝ) < exp (harmonic n : ℝ) * log (harmonic n : ℝ)


/-- With `p_ℓ` the `ℓ`-th prime (`p₁ = 2`), `1 ≤ j ≤ k + 1` and
`A(k) = ∏_{ℓ ≤ k + 1, ℓ ≠ j} (p_ℓ + 1)/p_ℓ` (the setup of Section 2.1),
`A(k) ≤ log(p_{k+1}) exp(c₁ - 1/p_j + 5/log p_{k+1})` for every `k`, where `c₁` is the
Meissel–Mertens constant (`≈ 0.261497`, the constant of Tenenbaum's Theorem 1.10 cited for it).

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 2
(`integers-2026-A86-lem-2`). -/
public theorem_wanted prod_succ_div_prime_le (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k + 1) :
    ∏ ℓ ∈ (Finset.Icc 1 (k + 1)).erase j,
        ((Nat.nth Nat.Prime (ℓ - 1) : ℝ) + 1) / Nat.nth Nat.Prime (ℓ - 1) ≤
      log (Nat.nth Nat.Prime k) *
        exp (meisselMertensConstant - 1 / (Nat.nth Nat.Prime (j - 1) : ℝ) +
          5 / log (Nat.nth Nat.Prime k))

/-- For `k ≥ 6` and `1 ≤ j ≤ k + 1`, `A(k) < C(k)` with
`C(k) = log((k+1)(log(k+1) + log log(k+1))) exp(c₁ - 1/p_j + 5/log((k+1)(log(k+1) + log log(k+1) - 1)))`,
`A(k)` as in `prod_succ_div_prime_le` and `c₁` the Meissel–Mertens constant.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 3
(`integers-2026-A86-lem-3`). -/
public theorem_wanted prod_succ_div_prime_lt_bound (k j : ℕ) (hk : 6 ≤ k) (hj : 1 ≤ j)
    (hjk : j ≤ k + 1) :
    ∏ ℓ ∈ (Finset.Icc 1 (k + 1)).erase j,
        ((Nat.nth Nat.Prime (ℓ - 1) : ℝ) + 1) / Nat.nth Nat.Prime (ℓ - 1) <
      log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)))) *
        exp (meisselMertensConstant - 1 / (Nat.nth Nat.Prime (j - 1) : ℝ) +
          5 / log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1)))

/-- For `j ∈ {1, 2, 3}` there is `K_j` such that `C(k) B(k) < e^γ D(k)` for all `k ≥ K_j`, where
`C(k)` is as in `prod_succ_div_prime_lt_bound`, `B(k) = ∏_{ℓ ≤ k + 1, ℓ ≠ j} p_ℓ²/(p_ℓ² - 1)` and
`D(k) = log((k+1)(log(k+1) + log log(k+1) - 1) log 2.51 - log p_j)`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Proposition 1
(`integers-2026-A86-prop-1`). -/
public theorem_wanted exists_bound_mul_prod_sq_lt_exp_eulerMascheroni_mul (j : ℕ) (hj : 1 ≤ j)
    (hj3 : j ≤ 3) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)))) *
          exp (meisselMertensConstant - 1 / (Nat.nth Nat.Prime (j - 1) : ℝ) +
            5 / log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1))) *
          ∏ ℓ ∈ (Finset.Icc 1 (k + 1)).erase j,
            (Nat.nth Nat.Prime (ℓ - 1) : ℝ) ^ 2 / ((Nat.nth Nat.Prime (ℓ - 1) : ℝ) ^ 2 - 1) <
        exp eulerMascheroniConstant *
          log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1) * log (251 / 100) -
            log (Nat.nth Nat.Prime (j - 1)))

/-- For `j ∈ {1, 2, 3}` there is `K_j` such that `C(k) B(k) < e^γ log log m` for all `k ≥ K_j`,
with `m = p_{k+1}# / p_j` and `C(k)`, `B(k)` as in
`exists_bound_mul_prod_sq_lt_exp_eulerMascheroni_mul`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 2
(`integers-2026-A86-thm-2`). -/
public theorem_wanted exists_bound_mul_prod_sq_lt_exp_eulerMascheroni_mul_log_log (j : ℕ)
    (hj : 1 ≤ j) (hj3 : j ≤ 3) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)))) *
          exp (meisselMertensConstant - 1 / (Nat.nth Nat.Prime (j - 1) : ℝ) +
            5 / log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1))) *
          ∏ ℓ ∈ (Finset.Icc 1 (k + 1)).erase j,
            (Nat.nth Nat.Prime (ℓ - 1) : ℝ) ^ 2 / ((Nat.nth Nat.Prime (ℓ - 1) : ℝ) ^ 2 - 1) <
        exp eulerMascheroniConstant *
          log (log ((primorial (Nat.nth Nat.Prime k) : ℝ) / Nat.nth Nat.Prime (j - 1)))

/-- For `k ≥ 13042`, `Ĉ(k) = exp(5/log((k+1)(log(k+1) + log log(k+1) - 1))) < 1.525` (`Ĉ` as
defined in the proof of Proposition 1).

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 5
(`integers-2026-A86-lem-5`). -/
public theorem_wanted exp_five_div_log_bound_lt (k : ℕ) (hk : 13042 ≤ k) :
    exp (5 / log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1))) < 1.525


/-- Let `p_ℓ` be the `ℓ`-th prime (`p₁ = 2`), `1 ≤ j ≤ k`, `q₁ < ⋯ < q_k` primes distinct from
`p_j`, `α_i ≥ 1` and `n = ∏ q_i^{α_i}`. Then
`σ(n)/n < ∏ q_i/(q_i - 1) = n/φ(n) ≤ ∏_{ℓ ≤ k + 1, ℓ ≠ j} p_ℓ/(p_ℓ - 1)`.
The paper prints the last link as strict; it is an equality when the `q_i` are exactly the first
`k` primes other than `p_j` (e.g. `j = k = 1`, `n = 3`: both sides are `3/2`), and the proof
(`p_i ≤ q_i`) gives `≤`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 1
(`integers-2026-A86-lem-1`). -/
public theorem_wanted sigma_div_lt_totient_ratio_le_prod_primes (k j : ℕ) (hj : 1 ≤ j)
    (hjk : j ≤ k) (q α : Fin k → ℕ) (hq : StrictMono q) (hqp : ∀ i, (q i).Prime)
    (hqj : ∀ i, q i ≠ Nat.nth Nat.Prime (j - 1)) (hα : ∀ i, 1 ≤ α i) :
    let n := ∏ i, q i ^ α i
    (ArithmeticFunction.sigma 1 n : ℝ) / n < ∏ i, (q i : ℝ) / (q i - 1) ∧
      ∏ i, (q i : ℝ) / (q i - 1) = (n : ℝ) / Nat.totient n ∧
      (n : ℝ) / Nat.totient n ≤
        ∏ ℓ ∈ (Finset.Icc 1 (k + 1)).erase j,
          (Nat.nth Nat.Prime (ℓ - 1) : ℝ) / (Nat.nth Nat.Prime (ℓ - 1) - 1)

end

end MetaMathlibExt
