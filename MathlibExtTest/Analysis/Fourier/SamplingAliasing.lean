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
open scoped FourierTransform

-- At spacing two, a shift of +1 cycle per unit time is an alias.
example : sampleSignal 2 (fun t ↦ (𝐞 (2 * t) : ℂ)) =
    sampleSignal 2 (fun t ↦ (𝐞 (1 * t) : ℂ)) := by
  have h := sampleSignal_complexExp_alias (T := 2) 1 2
  norm_num at h
  simpa only [one_mul] using h

-- At spacing two, a shift of -3/2 cycles per unit time is also an alias.
example : sampleSignal 2 (fun t ↦ (𝐞 ((1 + (-3 : ℝ) / 2) * t) : ℂ)) =
    sampleSignal 2 (fun t ↦ (𝐞 (1 * t) : ℂ)) := by
  simpa only [Int.cast_neg, Int.cast_ofNat] using sampleSignal_complexExp_alias (T := 2) 1 (-3)

-- Half a sampling frequency is not an alias of zero.
example : sampleSignal 1 (fun t ↦ (𝐞 ((1 / 2) * t) : ℂ)) ≠
    sampleSignal 1 (fun t ↦ (𝐞 (0 * t) : ℂ)) := by
  intro h
  obtain ⟨k, hk⟩ := (sampleSignal_complexExp_eq_iff (by norm_num)).mp h
  have hmul : (2 * k : ℝ) = 1 := by
    simp only [zero_add, div_one] at hk
    rw [← hk]
    norm_num
  have hint : (2 * k : ℤ) = 1 := by exact_mod_cast hmul
  omega

-- At zero spacing an integer shift divided by the step is zero; both sequences are one.
example : sampleSignal 0 (fun t ↦ (𝐞 ((1 + (3 : ℝ) / 0) * t) : ℂ)) = 1 := by
  calc
    _ = sampleSignal 0 (fun t ↦ (𝐞 (1 * t) : ℂ)) := by
      simpa only [Int.cast_ofNat] using sampleSignal_complexExp_alias (T := 0) 1 3
    _ = 1 := by
      funext n
      simp [sampleSignal]

-- The zero-step witness is not just zero on the grid: it also vanishes away from it.
example : sampleSignal 0 (samplingKernelSin 0) = 0 ∧ samplingKernelSin 0 5 = 0 :=
  ⟨sampleSignal_samplingKernelSin, by simp [samplingKernelSin]⟩

-- At spacing two, the kernel witness is zero on the grid and one at the midpoint.
example : sampleSignal 2 (samplingKernelSin 2) = 0 ∧ samplingKernelSin 2 1 = 1 := by
  refine ⟨sampleSignal_samplingKernelSin, ?_⟩
  have hhalf := samplingKernelSin_half_step (T := 2) (by norm_num)
  norm_num at hhalf ⊢
  exact hhalf

-- A negative step still aliases a shift of 1/T, and the witness is one at the negative midpoint.
example : sampleSignal (-2) (fun t ↦ (𝐞 ((-1 / 2) * t) : ℂ)) =
    sampleSignal (-2) (fun t ↦ (𝐞 (0 * t) : ℂ)) ∧
    samplingKernelSin (-2) (-1) = 1 := by
  refine ⟨(sampleSignal_complexExp_eq_iff (by norm_num)).mpr ⟨1, by norm_num⟩, ?_⟩
  have hhalf := samplingKernelSin_half_step (T := -2) (by norm_num)
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
