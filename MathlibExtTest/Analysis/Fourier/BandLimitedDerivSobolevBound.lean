/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.BandLimitedDerivSobolevBound

/-! # Tests for the band-limited Bernstein inequality -/

open Set
open scoped FourierTransform
open MathlibExt.Analysis.Fourier.BandLimitedDerivSobolevBoundWanted

example (s : ℝ) : dotHSeminorm s 0 = 0 := by
  simp [dotHSeminorm]

-- At the included endpoint the bandwidth factor reduces to a square root.
example : ∃ C > 0, ∀ (A : NNReal) (f : SchwartzMap ℝ ℂ),
    Function.support (fun ξ : ℝ ↦ (𝓕 f) ξ) ⊆ Icc (-(A : ℝ)) (A : ℝ) →
      sSup (range (fun x : ℝ ↦ ‖deriv f x‖)) ≤ C * Real.sqrt A * dotHSeminorm 1 f := by
  obtain ⟨C, hC, h⟩ := norm_deriv_le_rpow_mul_dotHSeminorm_of_fourier_support_Icc 1
    (by norm_num)
  refine ⟨C, hC, fun A f hf ↦ ?_⟩
  simpa only [show (3 / 2 - 1 : ℝ) = 1 / 2 by norm_num, Real.rpow_eq_pow, ← Real.sqrt_eq_rpow]
    using h A f hf

-- A spectrum supported at the origin gives a zero upper bound even for nonintegral s.
example (s : ℝ) (hs : s ∈ Ioc (1 / 2 : ℝ) 1) (f : SchwartzMap ℝ ℂ)
    (hf : Function.support (fun ξ : ℝ ↦ (𝓕 f) ξ) ⊆ {0}) :
    sSup (range (fun x : ℝ ↦ ‖deriv f x‖)) ≤ 0 := by
  obtain ⟨C, _, h⟩ := norm_deriv_le_rpow_mul_dotHSeminorm_of_fourier_support_Icc s hs
  have hpow : 3 / 2 - s ≠ 0 := by linarith [hs.2]
  simpa [Real.zero_rpow hpow] using h 0 f (by simpa using hf)
