/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.LindelofOfRiemannHypothesis

/-! # Specializations of the Lindelöf bound under the Riemann hypothesis -/

open Complex

-- On the critical line itself (the endpoint `σ = 1 / 2`).
example (hRH : RiemannHypothesis) :
    ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ |t| →
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ (1 / 100 : ℝ) := by
  obtain ⟨C, t₀, h⟩ :=
    MetaMathlibExt.zeta_le_rpow_of_riemannHypothesis hRH (1 / 100) (by norm_num)
  refine ⟨C, t₀, fun t ht => ?_⟩
  simpa using h (1 / 2) t le_rfl (by norm_num) ht

-- On the line `re s = 1` (the endpoint `σ = 1`).
example (hRH : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ |t| → ‖riemannZeta (1 + t * I)‖ ≤ C * |t| ^ ε := by
  obtain ⟨C, t₀, h⟩ := MetaMathlibExt.zeta_le_rpow_of_riemannHypothesis hRH ε hε
  refine ⟨C, t₀, fun t ht => ?_⟩
  simpa using h 1 t (by norm_num) le_rfl ht

-- A single bound for the whole strip `1 / 2 ≤ re s ≤ 1`, with the height threshold at least `1`
-- and the exponent `ε` as small as we like: `ζ(s) = O(|t| ^ ε)` uniformly in the strip.
example (hRH : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∃ C t₀ : ℝ, 1 ≤ t₀ ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → t₀ ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ ε := by
  obtain ⟨C, t₀, h⟩ := MetaMathlibExt.zeta_le_rpow_of_riemannHypothesis hRH ε hε
  refine ⟨C, max t₀ 1, le_max_right _ _, fun s h1 h2 ht => ?_⟩
  have := h s.re s.im h1 h2 ((le_max_left _ _).trans ht)
  rwa [re_add_im] at this

-- The reciprocal bound at `σ = 3 / 4` and `σ = 1`, uniformly on a vertical line, and for both
-- signs of `t`.
example (hRH : RiemannHypothesis) :
    ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ |t| →
      ‖(riemannZeta ((3 / 4 : ℝ) + t * I))⁻¹‖ ≤ C * |t| ^ (1 / 100 : ℝ) := by
  exact MetaMathlibExt.inv_zeta_le_rpow_of_riemannHypothesis hRH (3 / 4)
    (by norm_num) (by norm_num) (1 / 100) (by norm_num)

example (hRH : RiemannHypothesis) :
    ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ |t| →
      ‖(riemannZeta (1 + t * I))⁻¹‖ ≤ C * |t| ^ (1 / 100 : ℝ) := by
  simpa using MetaMathlibExt.inv_zeta_le_rpow_of_riemannHypothesis hRH 1
    (by norm_num) le_rfl (1 / 100) (by norm_num)

example (hRH : RiemannHypothesis) (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C t₀ : ℝ, 1 ≤ t₀ ∧ ∀ s : ℂ, s.re = σ → t₀ ≤ |s.im| →
      ‖(riemannZeta s)⁻¹‖ ≤ C * |s.im| ^ ε := by
  obtain ⟨C, t₀, h⟩ :=
    MetaMathlibExt.inv_zeta_le_rpow_of_riemannHypothesis hRH σ hσ hσ1 ε hε
  refine ⟨C, max t₀ 1, le_max_right _ _, fun s hs ht => ?_⟩
  have hbound := h s.im ((le_max_left _ _).trans ht)
  simpa only [← hs, re_add_im] using hbound

example (hRH : RiemannHypothesis) :
    ∃ C T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      ‖(riemannZeta ((3 / 4 : ℝ) + t * I))⁻¹‖ ≤ C * t ^ (1 / 100 : ℝ) ∧
      ‖(riemannZeta ((3 / 4 : ℝ) - t * I))⁻¹‖ ≤ C * t ^ (1 / 100 : ℝ) := by
  obtain ⟨C, t₀, h⟩ := MetaMathlibExt.inv_zeta_le_rpow_of_riemannHypothesis hRH (3 / 4)
    (by norm_num) (by norm_num) (1 / 100) (by norm_num)
  refine ⟨C, max t₀ 1, le_max_right _ _, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 1).trans ((le_max_right _ _).trans ht)
  have ht₀ : t₀ ≤ t := (le_max_left _ _).trans ht
  constructor
  · simpa only [abs_of_nonneg ht0] using h t (by simpa only [abs_of_nonneg ht0] using ht₀)
  · simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, abs_neg, abs_of_nonneg ht0]
      using h (-t) (by simpa only [abs_neg, abs_of_nonneg ht0] using ht₀)
