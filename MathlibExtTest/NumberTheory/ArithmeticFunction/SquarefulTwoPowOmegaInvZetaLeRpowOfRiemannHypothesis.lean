/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.SquarefulTwoPowOmegaInvZetaLeRpowOfRiemannHypothesis
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.Basic
import MathlibExt.NumberTheory.ArithmeticFunction.SquarefulTwoPowOmega
import MathlibExt.NumberTheory.KFull
import MathlibExt.NumberTheory.LSeries.LindelofOfRiemannHypothesis

/-! # Specializations of the reciprocal zeta bound under the Riemann hypothesis -/

open Complex

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.SquarefulTwoPowOmegaInvZetaLeRpowOfRiemannHypothesis

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

end MathlibExtTest.NumberTheory.ArithmeticFunction.SquarefulTwoPowOmegaInvZetaLeRpowOfRiemannHypothesis
