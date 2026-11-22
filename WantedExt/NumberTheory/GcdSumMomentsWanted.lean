/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import MathlibExt.NumberTheory.ArithmeticFunction.GcdSumTotient

/-!
# Moments of the mean gcd-sum function

Statements from M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for
the Gcd-Sum Function*, INTEGERS 26 (2026), Article A70: asymptotic formulas for
`∑_{n ≤ x} A(n)^k`, where `A(n) = P(n)/n` and `P(n) = ∑_{j=1}^n gcd(j, n)` is Pillai's gcd-sum
function, the structure of the Dirichlet series `F_k(s) = ∑ A(n)^k n^{-s}`, and the quoted
moment and pointwise bounds for `ζ` the proofs use. Lemmas 1, 4 and 6 of the paper are stated in
`WantedExt/NumberTheory/ZetaSubconvexityBoundsWanted.lean`.

The paper's main term `M_k(x)` is the residue of `F_k(s) x^s / s` at the pole of order `2^k`
at `s = 1`, so it has the form `x P(log x)` for a real polynomial `P`; the asymptotic theorems
below assert the existence of such a `P`. Since every stated error term is `o(x)`, the
polynomial is unique, so the existential form loses nothing.
-/

namespace MetaMathlibExt

@[expose] public section

open Complex Filter Asymptotics Polynomial

/-- The mean gcd-sum function `A(n) = P(n)/n`, where `P(n) = ∑_{j=1}^n gcd(j, n)` is Pillai's
gcd-sum function (`A(0) = 0` by the convention `x / 0 = 0`).

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (definition of `A(n)`). -/
noncomputable def gcdSumMean (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 n, (Nat.gcd j n : ℝ)) / n

/-- `A(1) = 1`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (definition of `A(n)`). -/
theorem gcdSumMean_one : gcdSumMean 1 = 1 := by
  simp [gcdSumMean]

/-- `A(2) = 3/2`, since `P(2) = gcd(1, 2) + gcd(2, 2) = 3`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (definition of `A(n)`). -/
theorem gcdSumMean_two : gcdSumMean 2 = 3 / 2 := by
  rw [gcdSumMean, show Finset.Icc 1 2 = {1, 2} by decide]
  norm_num

/-- `A(n) = ∑_{d ∣ n} φ(d)/d` for `n ≥ 1`, the divisor-sum form the paper records next to the
definition.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (Pillai's identity). -/
theorem gcdSumMean_eq_sum_totient_div {n : ℕ} (hn : 0 < n) :
    gcdSumMean n = ∑ d ∈ n.divisors, (Nat.totient d : ℝ) / d := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (gcd_sum_eq_totient_sum n hn)
  push_cast at h
  rw [gcdSumMean, h]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- **Theorem 1** (`k = 2`). There are a real polynomial `P` and a constant `C` with
`∑_{n ≤ x} A(n)^2 = x P(log x) + O(x^{1/2} exp(C (log log x)^2))` as `x → ∞`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 1 (`integers-2026-A70-thm-1`). -/
public theorem_wanted sum_gcdSumMean_sq_asymptotic :
    ∃ (P : ℝ[X]) (C : ℝ),
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, gcdSumMean n ^ 2 - x * P.eval (Real.log x))
        =O[atTop] fun x => x ^ (1 / 2 : ℝ) * Real.exp (C * Real.log (Real.log x) ^ 2)

/-- **Theorem 2** (`k = 3`). There are a real polynomial `P` and a constant `C` with
`∑_{n ≤ x} A(n)^3 = x P(log x) + O(x^{5/8} exp(C (log log x)^2))` as `x → ∞`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 2 (`integers-2026-A70-thm-2`). -/
public theorem_wanted sum_gcdSumMean_cube_asymptotic :
    ∃ (P : ℝ[X]) (C : ℝ),
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, gcdSumMean n ^ 3 - x * P.eval (Real.log x))
        =O[atTop] fun x => x ^ (5 / 8 : ℝ) * Real.exp (C * Real.log (Real.log x) ^ 2)

/-- **Theorem 3** (`k = 4`). There is a real polynomial `P` such that for every `ε > 0`,
`∑_{n ≤ x} A(n)^4 = x P(log x) + O_ε(x^{157/199 + ε})` as `x → ∞`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 3 (`integers-2026-A70-thm-3`). -/
public theorem_wanted sum_gcdSumMean_pow_four_asymptotic :
    ∃ P : ℝ[X], ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, gcdSumMean n ^ 4 - x * P.eval (Real.log x))
        =O[atTop] fun x => x ^ (157 / 199 + ε)

/-- **Theorem 4** (`k ≥ 5`). For each fixed `k ≥ 5` there is a real polynomial `P` such that
for every `ε > 0`,
`∑_{n ≤ x} A(n)^k = x P(log x) + O_{k,ε}(x^{1 + 2ε - 42/(13 · 2^k - 9)})` as `x → ∞`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 4 (`integers-2026-A70-thm-4`). -/
public theorem_wanted sum_gcdSumMean_pow_asymptotic (k : ℕ) (hk : 5 ≤ k) :
    ∃ P : ℝ[X], ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, gcdSumMean n ^ k - x * P.eval (Real.log x))
        =O[atTop] fun x => x ^ (1 + 2 * ε - 42 / (13 * 2 ^ k - 9))

/-- **Lemma 8** (structure of `F_k`). For every `k`, there are Dirichlet series
`G_k(s) = ∑ g(n) n^{-s}`, absolutely convergent for `ℜ s > 1/2`, and
`G̃_{k,2}(s) = ∑ h(n) n^{-s}`, absolutely convergent for `ℜ s > 1/3`, with
`∑ A(n)^k n^{-s} = ζ(s)^{2^k} G_k(s)` and `G_k(s) ζ(2s)^{4^k - 3^k - C(2^k, 2)} = G̃_{k,2}(s)`
for `ℜ s > 1`. The exponent is a natural number (`3^k + C(2^k, 2) ≤ 4^k`). The explicit Euler
product (3) for `G̃_{k,2}` is not stated.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 8 (`integers-2026-A70-lem-8`). -/
public theorem_wanted LSeries_gcdSumMean_pow_eq_riemannZeta_pow_mul (k : ℕ) :
    ∃ g h : ℕ → ℂ, (∀ s : ℂ, 1 / 2 < s.re → LSeriesSummable g s) ∧
      (∀ s : ℂ, 1 / 3 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n => ((gcdSumMean n ^ k : ℝ) : ℂ)) s = riemannZeta s ^ (2 ^ k) * LSeries g s ∧
        LSeries g s * riemannZeta (2 * s) ^ (4 ^ k - 3 ^ k - (2 ^ k).choose 2) = LSeries h s

/-- **Theorem 5**, vanishing of the exponents `ℓ_m`: for `m ≥ 2^k - 1`,
`ℓ_m = ∑_{r=0}^{2^k} (-1)^r C(2^k, r) (m + 1 - r)^k = 0`.

The sum is truncated at `r ≤ m + 1` (the coefficient of `p^{-ms}` in
`(1 - p^{-s})^{2^k} ∑_a (a + 1)^k p^{-as}`, read off from (3)); for `m ≥ 2^k - 1` the truncation
is vacuous. The printed untruncated sum vanishes for every `m` (a `2^k`-th difference of a
polynomial of degree `k`), which contradicts the paper's own `ℓ_2 = 3^k - 4^k + C(2^k, 2)`
(the exponent in (2) and (3)): at `k = 2`, `m = 2` the printed sum is `0` but the truncated sum is
`-1`. With the truncation the hypothesis `m ≥ 2^k - 1` is needed (`k = 2`, `m = 2`). The paper's
`k ≥ 2` is kept: at `k = 0` the `r = m + 1` term contributes `0^0 = 1` instead of the vanishing
coefficient of a negative index, so the truncated sum is no longer the coefficient of (3).

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 5 (`integers-2026-A70-thm-5`). -/
public theorem_wanted alternating_choose_two_pow_mul_pow_eq_zero (k m : ℕ) (hk : 2 ≤ k)
    (hm : 2 ^ k - 1 ≤ m) :
    ∑ r ∈ Finset.range (min (2 ^ k) (m + 1) + 1),
      (-1 : ℤ) ^ r * ((2 ^ k).choose r : ℤ) * ((m : ℤ) + 1 - r) ^ k = 0

/-- **Theorem 5**, the case `k = 2`: `F_2(s) = ζ(s)^4 / ζ(2s) · G̃_{2,2}(s)` for `ℜ s > 1`,
where `G̃_{2,2}(s) = ∑ h(n) n^{-s}` converges absolutely in every half-plane `ℜ s > 1/n`, that
is, for `ℜ s > 0`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 5 (`integers-2026-A70-thm-5`). -/
public theorem_wanted LSeries_gcdSumMean_sq_eq_riemannZeta_pow_four_div :
    ∃ h : ℕ → ℂ, (∀ s : ℂ, 0 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n => ((gcdSumMean n ^ 2 : ℝ) : ℂ)) s =
          riemannZeta s ^ 4 / riemannZeta (2 * s) * LSeries h s

/-- **Lemma 2** (quoted from Ivić). `∫_{T/2}^T |ζ(5/8 + i t)|^8 dt ≪ T (log T)^{38}` for all
sufficiently large `T`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 2 (`integers-2026-A70-lem-2`). -/
public theorem_wanted riemannZeta_eighth_moment_five_eighths_le :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∫ t in T / 2..T, ‖riemannZeta (5 / 8 + t * I)‖ ^ 8 ≤ C * T * Real.log T ^ 38

/-- **Lemma 3** (quoted twelfth-moment asymptotic). For fixed `5/7 < σ < 1` and every `ε > 0`,
`∫_1^T |ζ(σ + i t)|^{12} dt = T ∑_{n ≥ 1} d_6(n)^2 n^{-2σ} + O(T^{(9 - 7σ)/4 + ε})`, where
`d_6 = ζ^{*6}` is the six-fold divisor function. The printed side condition `|t| ≥ 1` is implied
by the integration range and omitted.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 3 (`integers-2026-A70-lem-3`). -/
public theorem_wanted riemannZeta_twelfth_moment_asymptotic {σ : ℝ} (hσ₁ : 5 / 7 < σ)
    (hσ₂ : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    (fun T : ℝ => ∫ t in (1 : ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 12 -
        T * ∑' n : ℕ,
          ((ArithmeticFunction.zeta ^ 6 : ArithmeticFunction ℕ) n : ℝ) ^ 2 / (n : ℝ) ^ (2 * σ))
      =O[atTop] fun T => T ^ ((9 - 7 * σ) / 4 + ε)

/-- **Lemma 5** (quoted). `∫_{10}^T |ζ(1/2 + i t)|^4 / |ζ(1 + 2 i t)| dt ≪ T (log T)^5` for
all sufficiently large `T`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 5 (`integers-2026-A70-lem-5`). -/
public theorem_wanted riemannZeta_fourth_moment_div_le :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∫ t in (10 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 / ‖riemannZeta (1 + 2 * t * I)‖ ≤
        C * T * Real.log T ^ 5

/-- **Lemma 7** (quoted, Ramachandra–Sankaranarayanan). There are constants `C` and `U₀` such
that for every `U ≥ U₀` some `T* ∈ (U, 2U)` satisfies
`|ζ(σ ± i T*)| ≤ exp(C (log log U)^2)` for all `σ ≥ 1/2`. The trailing `≪ U^ε` is a
consequence and is not stated.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 7 (`integers-2026-A70-lem-7`). -/
public theorem_wanted exists_riemannZeta_norm_le_exp_loglog_sq :
    ∃ C U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → ∃ T ∈ Set.Ioo U (2 * U), ∀ σ : ℝ, 1 / 2 ≤ σ →
      ‖riemannZeta (σ + T * I)‖ ≤ Real.exp (C * Real.log (Real.log U) ^ 2) ∧
        ‖riemannZeta (σ - T * I)‖ ≤ Real.exp (C * Real.log (Real.log U) ^ 2)

end

end MetaMathlibExt
