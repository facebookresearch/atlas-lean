/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.Analysis.SpecialFunctions.DickmanDeBruijn
public import MathlibExt.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
public import WantedExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumWanted

/-!
# Explicit prime-sum and mean-value estimates from Bordignon--Francis

Statement-only targets from Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to
the Burgess Bound via Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66. The statement texts
were checked against the preprint arXiv:2007.08119v1, whose numbering is shifted (Lemma 2.1,
Lemma 3.1, Propositions 4.4 and 4.5, Lemmas 4.7, 4.9 and 4.10).
-/

open Real

namespace MetaMathlibExt

@[expose] public section

/-- Explicit lower bound for the Dickman function: `ρ(x) ≥ x^(-1.42 x)` for `x ≥ 1`. The Dickman
function is pinned by the repository predicate `Real.IsDickmanDeBruijn` (normalization on
`[0, 1]` and `x ρ'(x) + ρ(x - 1) = 0` for `x > 1`).

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 2 (`integers-2024-A66-lem-2`). -/
public theorem_wanted dickman_ge_rpow_neg_mul {ρ : ℝ → ℝ} (hρ : Real.IsDickmanDeBruijn ρ)
    {x : ℝ} (hx : 1 ≤ x) :
    x ^ (-(1.42 : ℝ) * x) ≤ ρ x

/-- Near the pole, the logarithmic derivative of the Riemann zeta function satisfies
`|ζ'/ζ(s)| ≤ 1/|s - 1| + O(1)` uniformly for `s = 1 + α + iτ` with `α → 0⁺` and `|τ| ≤ 1/2`;
"`α ↘ 0`" is read as: for all `0 < α < α₀`, with one constant `C`.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 3 (`integers-2024-A66-lem-3`). -/
public theorem_wanted exists_norm_logDeriv_riemannZeta_le_inv_norm_add :
    ∃ C α₀ : ℝ, 0 < α₀ ∧ ∀ α τ : ℝ, 0 < α → α < α₀ → |τ| ≤ 1 / 2 →
      ‖deriv riemannZeta (1 + α + τ * Complex.I) / riemannZeta (1 + α + τ * Complex.I)‖ ≤
        1 / ‖(α : ℂ) + τ * Complex.I‖ + C

/-- Mertens' second theorem with the Rosser--Schoenfeld error: the Meissel--Mertens constant
`M = meisselMertensConstant` satisfies `0.2614 ≤ M < 0.2615` and
`|∑_{p ≤ x} 1/p - log log x - M| ≤ 1 / log² x` for every real `x > 1`.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Proposition 1
(`integers-2024-A66-prop-1`). -/
public theorem_wanted abs_sum_inv_primes_sub_meisselMertensConstant_le :
    0.2614 ≤ meisselMertensConstant ∧ meisselMertensConstant < 0.2615 ∧ ∀ x : ℝ, 1 < x →
      |(∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) - log (log x) -
          meisselMertensConstant| ≤ 1 / log x ^ 2

/-- Two-sided explicit Mertens bound: for real `x ≥ 2`,
`log log x + 0.2614 ≤ ∑_{p ≤ x} 1/p ≤ log log x + 0.8666`.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Proposition 2
(`integers-2024-A66-prop-2`). -/
public theorem_wanted log_log_add_le_sum_inv_primes_le {x : ℝ} (hx : 2 ≤ x) :
    log (log x) + 0.2614 ≤ ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p ∧
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p ≤ log (log x) + 0.8666

/-- With `K ≈ 0.3286` the solution of `(2π)⁻¹ ∫₀^{2π} |cos t - K| dt = 1 - K`, uniformly for
`0 < α ≤ 1` and real `τ`,
`∑_{p ≤ exp(1/α)} |cos(τ log p) - K| / p ≤ (1 - K) log(1/α) + (2 + 2K) log log(|τ| + 3) + 7.28`.
The defining equation of `K` has exactly one real solution, so the hypothesis pins `K`.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 7 (`integers-2024-A66-lem-7`). -/
public theorem_wanted sum_abs_cos_sub_div_primes_le {K : ℝ}
    (hK : (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), |cos t - K| = 1 - K)
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) (τ : ℝ) :
    ∑ p ∈ (Finset.Iic ⌊exp (1 / α)⌋₊).filter Nat.Prime, |cos (τ * log p) - K| / p ≤
      (1 - K) * log (1 / α) + (2 + 2 * K) * log (log (|τ| + 3)) + 7.28

/-- For real prime values `g(p)` with `|g(p)| ≤ 1`, `0 < α ≤ 1`, and `λ` defined by
`∑_{p ≤ exp(1/α)} (1 - g(p))/p = λ ∑_{p ≤ exp(1/α)} 1/p`, for every real `τ`,
`Re ∑_{p ≤ exp(1/α)} g(p)/p^{1+iτ} ≤ (1 - Kλ) log(1/α) + (2 + 2K) log log(|τ| + 3) + C₀
+ (K - Kλ)(M + M'(exp(1/α)))` with `C₀ = 7.28` and `K` as in Lemma 7. The paper prints
`(2 + 2K)(log log |τ| + 3)`; its proof applies Lemma 7, which has `log log(|τ| + 3)`, and the
printed form fails at `α = 1`, `g ≡ 1`, `τ = 1.0001`. The paper's `α ∈ [0, 1]` is restricted to
`α > 0`, where `exp(1/α)` is defined. `M + M'(x)` is written per Proposition 1 as
`M + (∑_{p ≤ x} 1/p - log log x - M)` with `M = meisselMertensConstant`; the binder `lam` is `λ`.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 8 (`integers-2024-A66-lem-8`). -/
public theorem_wanted re_sum_div_primes_cpow_le {K : ℝ}
    (hK : (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), |cos t - K| = 1 - K)
    {g : ℕ → ℝ} (hg : ∀ p, p.Prime → |g p| ≤ 1) {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) {lam : ℝ}
    (hlam : ∑ p ∈ (Finset.Iic ⌊exp (1 / α)⌋₊).filter Nat.Prime, (1 - g p) / p =
      lam * ∑ p ∈ (Finset.Iic ⌊exp (1 / α)⌋₊).filter Nat.Prime, (1 : ℝ) / p) (τ : ℝ) :
    (∑ p ∈ (Finset.Iic ⌊exp (1 / α)⌋₊).filter Nat.Prime,
        (g p : ℂ) / (p : ℂ) ^ (1 + τ * Complex.I)).re ≤
      (1 - K * lam) * log (1 / α) + (2 + 2 * K) * log (log (|τ| + 3)) + 7.28 +
        (K - K * lam) * (meisselMertensConstant +
          ((∑ p ∈ (Finset.Iic ⌊exp (1 / α)⌋₊).filter Nat.Prime, (1 : ℝ) / p) -
            log (log (exp (1 / α))) - meisselMertensConstant))

/-- For a completely multiplicative arithmetic function `g` with `|g(n)| ≤ 1` and its Dirichlet series
`F(s) = ∑ g(n) n^{-s}`, for `Re s > 1`,
`|F(s)| ≤ exp(ν₂) · exp(Re ∑_p g(p)/p^s)` with `ν₂ ≤ 0.316`. The paper's `ν₂ = γ - M` is written
here as its prime-series form `∑_p (-log(1 - 1/p) - 1/p)` (the identity used in its proof).

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 9 (`integers-2024-A66-lem-9`). -/
public theorem_wanted norm_LSeries_le_exp_nu₂_mul_exp_re_sum_primes
    {g : ArithmeticFunction ℂ} (hg₁ : g 1 = 1) (hmul : g.IsCompletelyMultiplicative)
    (hg : ∀ n, ‖g n‖ ≤ 1) :
    (∑' p : Nat.Primes, (-log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))) ≤ 0.316 ∧
      ∀ s : ℂ, 1 < s.re →
        ‖LSeries (⇑g) s‖ ≤ exp (∑' p : Nat.Primes, (-log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))) *
          exp (∑' p : Nat.Primes, g p / (p : ℂ) ^ s).re

/-- Uniformly for `0 < α ≤ 1`, `∑_{p > exp(1/α)} p^{-(1 + α)} ≤ 0.9235`.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 10 (`integers-2024-A66-lem-10`). -/
public theorem_wanted tsum_rpow_neg_primes_gt_exp_inv_le {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    ∑' p : {p : ℕ // p.Prime ∧ exp (1 / α) < p}, ((p : ℕ) : ℝ) ^ (-(1 + α)) ≤ 0.9235

end

end MetaMathlibExt
