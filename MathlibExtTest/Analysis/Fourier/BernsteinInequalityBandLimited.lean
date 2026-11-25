/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.BernsteinInequalityBandLimited
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Endpoint tests for the Bernstein inequality -/

open MeasureTheory
open scoped FourierTransform ENNReal

namespace MathlibExtTest.Analysis.Fourier.BernsteinInequalityBandLimited

open MathlibExt.Analysis.Fourier.BernsteinInequalityBandLimitedWanted

-- The same constant works at both endpoints for a spectrum nonzero on the entire open unit ball.
example : ∃ f : SchwartzMap ℝ ℂ,
    Function.support (fun ξ : ℝ => (𝓕 f) ξ) = Metric.ball (0 : ℝ) 1 ∧
    ∃ C > 0, ‖(SchwartzMap.derivCLM ℂ ℂ f).toLp 1 volume‖ ≤ C * ‖f.toLp 1 volume‖ ∧
      ‖(SchwartzMap.derivCLM ℂ ℂ f).toLp ∞ volume‖ ≤ C * ‖f.toLp ∞ volume‖ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let χ : SchwartzMap ℝ ℂ := (b.hasCompactSupport.comp_left (g := Complex.ofRealCLM)
    (by simp)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let f : SchwartzMap ℝ ℂ := 𝓕⁻ χ
  have hs : Function.support (fun ξ : ℝ => (𝓕 f) ξ) = Metric.ball (0 : ℝ) 1 := by
    rw [show 𝓕 f = χ from FourierInvPair.fourier_fourierInv_eq χ, ← b.support_eq]
    ext ξ
    change ((b ξ : ℂ) ≠ 0) ↔ b ξ ≠ 0
    simp
  obtain ⟨C, hC, h⟩ := exists_norm_deriv_toLp_le_of_support_fourier_subset_ball
  exact ⟨f, hs, C, hC, h 1 le_rfl f hs.subset, h ∞ le_top f hs.subset⟩

end MathlibExtTest.Analysis.Fourier.BernsteinInequalityBandLimited
