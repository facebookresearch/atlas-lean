/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.NumberTheory.KFull

/-!
# Venkatasubbareddy–Sankaranarayanan, `2^{ω(n)}` on squareful integers — wishlist

Statement-only records for the lemmas of Venkatasubbareddy and
Sankaranarayanan, INTEGERS 24 (2024), Article A110, that are stated over
explicit objects: the factorizations of `F(s) = ∑_{n squareful} 2^{ω(n)} n^{-s}`
(squareful is `Nat.IsKFull 2`)
through zeta products (Lemmas 1 and 2) and the classical zeta estimates the
paper quotes (Lemmas 4, 5, 6 and 8). A positive integer `n` is squareful when
`p ∣ n` implies `p^2 ∣ n` for every prime `p`; `n = 1` is squareful. The
paper's Lemma 7 (`N(T) ≪ T log T`) is implied by
`MetaMathlibExt.bellotti_wong_zero_count_bound`.
-/

open Complex

namespace MetaMathlibExt

@[expose] public section

open Classical in
/-- Lemma 1: for `Re s > 1/2`,
`F(s) = ζ²(2s)ζ²(3s)ζ²(7s)ζ⁴(8s)ζ⁵(12s)ζ¹⁴(13s)ζ⁵(14s) /
(ζ(4s)ζ²(5s)ζ³(6s)ζ⁵(10s)ζ⁶(11s)) · H₁(s)`, where `H₁` is a Dirichlet series
converging absolutely for `Re s > 1/15`.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 1 (`integers-2024-A110-lem-1`). -/
public theorem_wanted squareful_two_pow_omega_LSeries_eq_zeta_quotient_fifteen :
    ∃ h : ℕ → ℂ, (∀ s : ℂ, 1 / 15 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        LSeries (fun n => if Nat.IsKFull 2 n then
            (2 : ℂ) ^ ArithmeticFunction.cardDistinctFactors n else 0) s =
          riemannZeta (2 * s) ^ 2 * riemannZeta (3 * s) ^ 2 * riemannZeta (7 * s) ^ 2 *
              riemannZeta (8 * s) ^ 4 * riemannZeta (12 * s) ^ 5 *
              riemannZeta (13 * s) ^ 14 * riemannZeta (14 * s) ^ 5 /
            (riemannZeta (4 * s) * riemannZeta (5 * s) ^ 2 * riemannZeta (6 * s) ^ 3 *
              riemannZeta (10 * s) ^ 5 * riemannZeta (11 * s) ^ 6) * LSeries h s

open Classical in
/-- Lemma 2: for `Re s > 1/2`, `F(s) = ζ²(2s)ζ²(3s)/ζ(4s) · H₂(s)`, where `H₂` is a
Dirichlet series converging absolutely for `Re s > 1/5`.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 2 (`integers-2024-A110-lem-2`). -/
public theorem_wanted squareful_two_pow_omega_LSeries_eq_zeta_quotient_five :
    ∃ h : ℕ → ℂ, (∀ s : ℂ, 1 / 5 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        LSeries (fun n => if Nat.IsKFull 2 n then
            (2 : ℂ) ^ ArithmeticFunction.cardDistinctFactors n else 0) s =
          riemannZeta (2 * s) ^ 2 * riemannZeta (3 * s) ^ 2 / riemannZeta (4 * s) * LSeries h s

/-- Lemma 4 (quoted classical result): uniformly for `1/2 ≤ σ ≤ 1` and large `T`,
`∫_1^T |ζ(σ + it)|⁴ dt ≪ T (log T)⁴`.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 4 (`integers-2024-A110-lem-4`). -/
public theorem_wanted zeta_fourth_moment_le_uniform :
    ∃ C T₀ : ℝ, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → ∀ T : ℝ, T₀ ≤ T →
      ∫ t in (1 : ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 4 ≤ C * T * Real.log T ^ 4

/-- Lemma 5 (quoted classical result, Vinogradov–Korobov): there is `C > 0` such
that `1/ζ(s) ≪ (log T)^{2/3} (log log T)^{1/3}` in the region
`σ ≥ 1 - C / ((log T)^{2/3} (log log T)^{1/3})`, `T₀ < t ≤ T`; `ζ(s) ≠ 0` is stated with
the bound, since Lean's `0⁻¹ = 0` would make the bound alone vacuous at a zero.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 5 (`integers-2024-A110-lem-5`). -/
public theorem_wanted inv_zeta_le_vinogradov_korobov :
    ∃ C K T₀ : ℝ, 0 < C ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, ∀ s : ℂ, T₀ < s.im → s.im ≤ T →
      1 - C / (Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3)) ≤ s.re →
        riemannZeta s ≠ 0 ∧ ‖(riemannZeta s)⁻¹‖ ≤
          K * Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3)

/-- Lemma 6 (quoted classical result, Vinogradov–Korobov zero-free region):
there is `C* > 0` with `ζ(s) ≠ 0` for
`σ ≥ 1 - C* / ((log |t|)^{2/3} (log log |t|)^{1/3})`, `|t| ≥ t₀`.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 6 (`integers-2024-A110-lem-6`). -/
public theorem_wanted zeta_ne_zero_vinogradov_korobov :
    ∃ C t₀ : ℝ, 0 < C ∧ 3 ≤ t₀ ∧ ∀ s : ℂ, t₀ ≤ |s.im| →
      1 - C / (Real.log |s.im| ^ ((2 : ℝ) / 3) *
          Real.log (Real.log |s.im|) ^ ((1 : ℝ) / 3)) ≤ s.re →
        riemannZeta s ≠ 0

/-- Lemma 8, equation (24) (quoted classical result): the Riemann hypothesis
implies `ζ(σ + it) = O(|t|^ε)` uniformly for `1/2 ≤ σ ≤ 1`, `|t| ≥ t₀`.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 8 (`integers-2024-A110-lem-8`). -/
public theorem_wanted zeta_le_rpow_of_riemannHypothesis (hRH : RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C t₀ : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → t₀ ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε

/-- Lemma 8, equation (25) (quoted classical result): the Riemann hypothesis
implies `1/ζ(σ + it) = O(|t|^ε)` for each fixed `1/2 < σ ≤ 1`, `|t| ≥ t₀`; the
constants depend on `σ` and `ε`.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 8 (`integers-2024-A110-lem-8`). -/
public theorem_wanted inv_zeta_le_rpow_of_riemannHypothesis (hRH : RiemannHypothesis)
    (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ |t| → ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ C * |t| ^ ε

open Classical in
/-- Theorem 1 (unconditional): with `f(n) = 2^{ω(n)}` for squareful `n` and `0` otherwise
(`f(1) = 1`), there are real constants `C₁, C₂, C₃, C₄` and `c > 0` with
`∑_{n ≤ x} f(n) = C₁ x^{1/2} log x + C₂ x^{1/2} + C₃ x^{1/3} log x + C₄ x^{1/3}
  + O(x^{1/4} exp(c (log x / log log x)^{1/3}))` for large `x`. The paper writes the
coefficient as `c_ε`, "for some `c > 0`", after "let `ε > 0`": a constant chosen after `ε`, not
a product with an arbitrarily small factor. Its proof (equations (28)-(30)) produces the
exponent `(4 + ε) c (log T / log log T)^{1/3}` with `ε` small and `c > 0` the fixed constant of
its contour shift to `Re s = 1/4 - c/g(T)`, `g(T) = (log T)^{2/3} (log log T)^{1/3}`, chosen in
terms of the Vinogradov-Korobov zero-free region and the bound for `1/ζ` there (its Lemmas 5 and
6), so the coefficient stays bounded away from `0` and the statement is one existential `c > 0`.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Theorem 1 (`integers-2024-A110-thm-1`). -/
public theorem_wanted squareful_two_pow_omega_sum_asymptotic :
    ∃ C₁ C₂ C₃ C₄ c K x₀ : ℝ, 0 < c ∧ ∀ x : ℝ, x₀ ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if Nat.IsKFull 2 n then
            (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n else 0) -
          (C₁ * x ^ ((1 : ℝ) / 2) * Real.log x + C₂ * x ^ ((1 : ℝ) / 2) +
            C₃ * x ^ ((1 : ℝ) / 3) * Real.log x + C₄ * x ^ ((1 : ℝ) / 3))| ≤
        K * x ^ ((1 : ℝ) / 4) *
          Real.exp (c * (Real.log x / Real.log (Real.log x)) ^ ((1 : ℝ) / 3))

end

end MetaMathlibExt
