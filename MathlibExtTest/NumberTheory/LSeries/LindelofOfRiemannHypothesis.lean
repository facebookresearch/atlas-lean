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
