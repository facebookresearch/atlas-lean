/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace MetaMathlibExt

@[expose] public section

/-! # The distribution of `φ(σ(n))`

Statements from Dixit and Bhattacharjee on how often `φ(σ(n))` is large compared with `n`.
`log_k` is the `k`-fold iterated natural logarithm, written out with `Real.log`. Counts run
over positive integers `n ≤ x`, i.e. `n ∈ Finset.Icc 1 ⌊x⌋₊`. The paper's Lemma 2
(Siegel–Walfisz in prime-counting form) is already stated as
`MathlibExt.NumberTheory.PrimeCounting.UniformPrimeCountingWanted.uniform_prime_counting_arithmetic_progression`.
-/

open Filter Asymptotics

open Classical in
/-- The Pollack–Pomerance sieve bound quoted by the paper: uniformly in the set of primes `P`
and in `x > 1`, the proportion of positive integers `n ≤ x` with no prime factor in `P` is
`O(exp(-A(x)))`, where `A(x) = ∑_{p ≤ x, p ∈ P} 1/p`. Stated with an absolute constant `C`
as `#{n ≤ x : n free of P} ≤ C · x · exp(-A(x))`.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Lemma 1 (`integers-2024-A65-lem-1`), quoting Pollack and
Pomerance, Lemma 3. -/
public theorem_wanted card_free_of_prime_set_le_exp_neg_sum_inv :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Set ℕ), (∀ p ∈ P, p.Prime) → ∀ x : ℝ, 1 < x →
      ((((Finset.Icc 1 ⌊x⌋₊).filter fun n => ∀ p ∈ P, ¬ p ∣ n).card : ℕ) : ℝ) ≤
        C * x * Real.exp (-∑ p ∈ (Finset.Iic ⌊x⌋₊).filter (· ∈ P), (1 : ℝ) / p)

/-- For every prime `p` and every `x ≥ e^p`, the number `S_p(x)` of positive integers
`n ≤ x` with `p ∤ σ(n)` is `O(x (log log x / log x)^(1/(p-1)))`, with an absolute implied
constant.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Lemma 3 (`integers-2024-A65-lem-3`). -/
public theorem_wanted card_not_dvd_sigma_le :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∀ x : ℝ, Real.exp p ≤ x →
      ((((Finset.Icc 1 ⌊x⌋₊).filter fun n => ¬ p ∣ ArithmeticFunction.sigma 1 n).card : ℕ) :
          ℝ) ≤
        C * x * (Real.log (Real.log x) / Real.log x) ^ ((1 : ℝ) / ((p : ℝ) - 1))

/-- For every `c > 0`,
`#{n ≤ x : φ(σ(n)) ≥ c n} ≤ π² x / (6 c log₄ x) + O(x log₃ x / ((log x)^(1/log₃ x) log₄ x))`,
with the implied constant depending only on `c`. The bound is stated for all sufficiently
large `x` (it needs `log₄ x > 0`, i.e. `x > e^(e^e)`). The record's follow-up remarks are
not part of the statement.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Theorem 1 (`integers-2024-A65-thm-1`). -/
public theorem_wanted card_totient_sigma_ge_mul_le (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ᶠ x in atTop,
      ((((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
          c * n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ) ≤
        Real.pi ^ 2 * x / (6 * c * Real.log (Real.log (Real.log (Real.log x)))) +
          C * (x * Real.log (Real.log (Real.log x)) /
            (Real.log x ^ (1 / Real.log (Real.log (Real.log x))) *
              Real.log (Real.log (Real.log (Real.log x)))))

/-- Let `f : ℝ⁺ → ℝ⁺` be non-decreasing with `f(x) = o(log₄ x)`, and let
`P_f(x) = {n ≤ x : φ(σ(n)) ≥ n / f(n)}`. Then
`|P_f(x)| = O(x f(x) / log₄ x + x log₃ x / ((log x)^(1/log₃ x) log₄ x))` and
`|P_f(x)| = o(x)` as `x → ∞`. The function is taken on `ℝ`, with positivity and
monotonicity required on `(0, ∞)` only.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Theorem 2 (`integers-2024-A65-thm-2`). -/
public theorem_wanted card_totient_sigma_ge_div_isBigO (f : ℝ → ℝ)
    (hpos : ∀ x, 0 < x → 0 < f x) (hmono : MonotoneOn f (Set.Ioi 0))
    (hf : f =o[atTop] fun x => Real.log (Real.log (Real.log (Real.log x)))) :
    ((fun x : ℝ => ((((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
        (n : ℝ) / f n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ))
      =O[atTop] fun x =>
        x * f x / Real.log (Real.log (Real.log (Real.log x))) +
          x * Real.log (Real.log (Real.log x)) /
            (Real.log x ^ (1 / Real.log (Real.log (Real.log x))) *
              Real.log (Real.log (Real.log (Real.log x))))) ∧
    ((fun x : ℝ => ((((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
        (n : ℝ) / f n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ))
      =o[atTop] fun x => x)

/-- Except for `O(x log₅ x / log₄ x)` positive integers `n ≤ x`, `φ(σ(n)) ≤ n / log₅ n`.
The finitely many small `n` for which `log₅ n` is not a positive real are absorbed by the
`O`-term.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Corollary 1 (`integers-2024-A65-cor-1`). -/
public theorem_wanted card_totient_sigma_gt_div_log_five_isBigO :
    (fun x : ℝ => ((((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
        (n : ℝ) / Real.log (Real.log (Real.log (Real.log (Real.log n)))) <
          (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ))
      =O[atTop] fun x =>
        x * Real.log (Real.log (Real.log (Real.log (Real.log x)))) /
          Real.log (Real.log (Real.log (Real.log x)))

end

end MetaMathlibExt
