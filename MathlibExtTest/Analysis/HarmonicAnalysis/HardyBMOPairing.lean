/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.HarmonicAnalysis.HardyBMOPairing

/-!
# Tests for Fefferman's Hardy space pairing inequality

Apply the pairing estimate to the difference of the indicators of two adjacent unit intervals.
-/

open MathlibExt.Analysis.HarmonicAnalysis.BoundedMeanOscillationWanted MeasureTheory Set
open scoped ENNReal

namespace MathlibExtTest.Analysis.HarmonicAnalysis.HardyBMOPairing

private noncomputable def step (a c : ℝ) : ℝ → ℝ := (Ioc a c).indicator fun _ => 1

private noncomputable def signedStep (x : ℝ) : ℝ := step 0 1 x - step 1 2 x

private theorem measurable_step (a c : ℝ) : Measurable (step a c) :=
  measurable_const.indicator measurableSet_Ioc

private theorem integrable_step (a c : ℝ) : Integrable (step a c) := by
  have hfin : volume (Ioc a c) ≠ ∞ := by simp [Real.volume_Ioc]
  exact (integrableOn_const (C := (1 : ℝ)) hfin).integrable_indicator measurableSet_Ioc

private theorem integral_step (a c : ℝ) (h : a ≤ c) : (∫ x, step a c x) = c - a := by
  rw [step, integral_indicator measurableSet_Ioc, setIntegral_const, Real.volume_real_Ioc_of_le h,
    smul_eq_mul, mul_one]

private theorem signedStep_mean_zero : (∫ x, signedStep x) = 0 := by
  unfold signedStep
  rw [integral_sub (integrable_step _ _) (integrable_step _ _), integral_step 0 1 (by norm_num),
    integral_step 1 2 (by norm_num)]
  norm_num

private theorem signedStep_bound (x : ℝ) : |signedStep x| ≤ 1 := by
  classical
  by_cases h : x ∈ Ioc (0 : ℝ) 1 <;> by_cases h' : x ∈ Ioc (1 : ℝ) 2 <;>
    norm_num [signedStep, step, h, h']

private theorem signedStep_support : HasCompactSupport signedStep := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (0 : ℝ) 2) isCompact_Icc
  intro x hx
  by_contra h
  have h₀ : x ∉ Ioc (0 : ℝ) 1 := fun h₀ => h ⟨h₀.1.le, h₀.2.trans (by norm_num)⟩
  have h₁ : x ∉ Ioc (1 : ℝ) 2 := fun h₁ => h ⟨(by norm_num : (0 : ℝ) ≤ 1).trans h₁.1.le, h₁.2⟩
  exact hx (by simp [signedStep, step, h₀, h₁])

example : ∃ C : ℝ, 0 < C ∧ (∫ x, signedStep x) = 0 ∧
    ∀ b : ℝ → ℝ, LocallyIntegrable b → ∀ B : ℝ, 0 < B →
      (∀ a c : ℝ, a < c → ⨍ x in Icc a c, |b x - ⨍ y in Icc a c, b y| ≤ B) →
        ‖∫ x, signedStep x * b x‖ₑ ≤ ENNReal.ofReal (C * B) *
          ∫⁻ x, ⨆ t : ℝ, ⨆ (_ : 0 < t), ⨆ y : ℝ, ⨆ (_ : |y - x| ≤ t),
            ‖∫ z, t / (Real.pi * (t ^ 2 + (y - z) ^ 2)) * signedStep z‖ₑ := by
  obtain ⟨C, hC, h⟩ := exists_enorm_integral_mul_le_poissonMaximal
  refine ⟨C, hC, signedStep_mean_zero, ?_⟩
  intro b hb B hB hosc
  exact h b hb B hB hosc signedStep ((measurable_step _ _).sub (measurable_step _ _))
    ⟨1, signedStep_bound⟩ signedStep_support

end MathlibExtTest.Analysis.HarmonicAnalysis.HardyBMOPairing
