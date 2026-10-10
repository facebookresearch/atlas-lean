/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.TorusSobolev.Fourier
import MathlibExt.Analysis.Fourier.TorusSobolev.Extremals
import MathlibExt.Analysis.Fourier.TorusSobolev.LogarithmicBounds

open TorusSobolev

noncomputable section

example : ConditionalAdmissible lowestShellWitness 1 := lowestShellWitness_admissible

example : mean lowestShellWitness = 0 := mean_lowestShellWitness

example : gradientEnergy lowestShellWitness = 1 := gradientEnergy_lowestShellWitness

example : laplaceEnergy lowestShellWitness = 1 := laplaceEnergy_lowestShellWitness

example : lowestShellWitness 0 = 1 / Real.pi := lowestShellWitness_at_zero

example : fourierCoefficient lowestShellWitness (axisFrequency 0) = (1 / 2 : ℂ) := by
  classical
  simp [fourierCoefficient_lowestShellWitness, lowestShell]

example : fourierCoefficient lowestShellWitness (0 : Frequency) = 0 := by
  classical
  norm_num [fourierCoefficient_lowestShellWitness, lowestShell, axisFrequency,
    funext_iff, Fin.forall_fin_two]

example : 0 < gradientEnergy lowestShellWitness := by
  rw [gradientEnergy_lowestShellWitness]
  exact zero_lt_one

example : frequencyRatio lowestShellWitness = 1 := by
  simp [frequencyRatio, laplaceEnergy_lowestShellWitness, gradientEnergy_lowestShellWitness]

example : (((1 / Real.pi) ^ 2 : ℝ) : EReal) ∈ conditionalPointValues 1 := by
  refine ⟨lowestShellWitness, lowestShellWitness_admissible, ?_⟩
  change (((lowestShellWitness 0) ^ 2 : ℝ) : EReal) = (((1 / Real.pi) ^ 2 : ℝ) : EReal)
  rw [lowestShellWitness_at_zero]

example : theta 1 ≤ (0 : EReal) → (((1 / Real.pi) ^ 2 : ℝ) : EReal) ≤ 0 := by
  intro h
  have hx := (theta_le_iff 1 0).mp h lowestShellWitness lowestShellWitness_admissible
  simpa only [lowestShellWitness_at_zero] using hx

example (b : EReal) :
    sharpRemainderValue ≤ b ↔ ∀ δ : ℝ, 1 ≤ δ → remainder δ ≤ b :=
  sharpRemainderValue_le_iff b

example : remainder 1 ∈ sharpRemainderValues := ⟨1, le_rfl, rfl⟩

example : KernelAdmissible ExtremalParameter.firstShell := True.intro

example : extremalCoefficient .firstShell True.intro (axisFrequency 1) = (Real.pi : ℂ) := by
  norm_num [extremalCoefficient, frequencyWeight, axisFrequency, Fin.sum_univ_two]

example : extremalCoefficient .firstShell True.intro (0 : Frequency) = 0 := by
  norm_num [extremalCoefficient, frequencyWeight]
