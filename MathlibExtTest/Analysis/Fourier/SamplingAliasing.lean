/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.SamplingAliasing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- At spacing two, a shift of -3/2 cycles per unit time is an alias.
example : sampleSignal 2 (complexExpSignal (1 + (-3 : ℝ) / 2)) =
    sampleSignal 2 (complexExpSignal 1) := by
  simpa only [Int.cast_neg, Int.cast_ofNat] using
    sampleSignal_complexExp_alias (T := 2) (by norm_num) 1 (-3)

-- Half a sampling frequency is not an alias of zero.
example : sampleSignal 1 (complexExpSignal (1 / 2)) ≠ sampleSignal 1 (complexExpSignal 0) := by
  intro h
  obtain ⟨k, hk⟩ := (sampleSignal_complexExp_eq_iff (by norm_num)).mp h
  have hmul : (2 * k : ℝ) = 1 := by
    simp only [zero_add, div_one] at hk
    rw [← hk]
    norm_num
  have hint : (2 * k : ℤ) = 1 := by exact_mod_cast hmul
  omega

-- The kernel witness is invisible on the whole grid, but equals one at its midpoint.
example : sampleSignal 2 (samplingKernelSin 2) = 0 ∧ samplingKernelSin 2 1 = 1 := by
  refine ⟨sampleSignal_samplingKernelSin (by norm_num), ?_⟩
  have hhalf := samplingKernelSin_half_step (T := 2) (by norm_num)
  norm_num at hhalf ⊢
  exact hhalf

-- The period-four sine sampled at spacing one folds the index -3 onto index 1.
example : ∃ y : ZMod 4 → ℂ, (∀ n : ℤ, y (n : ZMod 4) = sampleSignal 1 (samplingKernelSin 2) n) ∧
    y ((-3 : ℤ) : ZMod 4) = 1 := by
  have hp : Function.Periodic (samplingKernelSin 2) ((4 : ℝ) * 1) := by
    intro t
    unfold samplingKernelSin
    rw [show Real.pi * (t + 4 * 1) / 2 = Real.pi * t / 2 + 2 * Real.pi by ring,
      Real.sin_periodic _]
  obtain ⟨y, hy, _⟩ := sampleSignal_factors_zmod (N := 4) hp
  refine ⟨y, hy, ?_⟩
  have hfold : ((-3 : ℤ) : ZMod 4) = ((1 : ℤ) : ZMod 4) := by decide
  rw [hfold, hy]
  simpa [sampleSignal] using samplingKernelSin_half_step (T := 2) (by norm_num)
