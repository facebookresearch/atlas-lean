/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.HighFrequencySupNormSobolevBound

/-!
# Tests for the high-frequency sup-norm bound
-/

open MeasureTheory Set
open scoped FourierTransform
open MathlibExt.Analysis.Fourier.HighFrequencySupNormSobolevBoundWanted

/-- At order zero, Plancherel recovers the ordinary spatial L² norm. -/
example (f : SchwartzMap ℝ ℂ) :
    dotHSeminorm 0 f = Real.sqrt (∫ x, ‖f x‖ ^ 2) := by
  simp [dotHSeminorm, SchwartzMap.integral_norm_sq_fourier]

/-- At the included endpoint, a nonzero value forces positive homogeneous Sobolev seminorm. -/
example (A : NNReal) (hA : 0 < (A : ℝ)) (f : SchwartzMap ℝ ℂ)
    (hf : tsupport (fun ξ : ℝ => (𝓕 f) ξ) ⊆ (Icc (-(A : ℝ)) (A : ℝ))ᶜ)
    (x : ℝ) (hx : f x ≠ 0) : 0 < dotHSeminorm 1 f := by
  obtain ⟨C, hC, h⟩ :=
    sSup_norm_le_rpow_mul_dotHSeminorm_of_tsupport_fourier_compl_Icc 1 (by
      constructor <;> norm_num)
  have hsup : ‖f x‖ ≤ sSup (range (fun y : ℝ ↦ ‖f y‖)) :=
    le_csSup f.toBoundedContinuousFunction.bddAbove_range_norm_comp (mem_range_self x)
  by_contra! hzero
  exact (norm_pos_iff.mpr hx).not_ge <| hsup.trans <| (h A hA f hf).trans <|
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hC.le (Real.rpow_nonneg hA.le _)) hzero
