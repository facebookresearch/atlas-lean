/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Longitudinal.LinearDegradation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.NormNum

/-! # Two-time identifiability with a shared noise draw -/

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics

private noncomputable def sharedNoise : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).map (fun z : ℝ => (z, z))

private instance : IsProbabilityMeasure sharedNoise := by
  unfold sharedNoise
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

private theorem sharedNoise_fst : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal 0 1) sharedNoise := by
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  rw [sharedNoise, Measure.map_map measurable_fst (by fun_prop)]
  exact Measure.map_id

private theorem sharedNoise_snd : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal 0 1) sharedNoise := by
  refine ⟨measurable_snd.aemeasurable, ?_⟩
  rw [sharedNoise, Measure.map_map measurable_snd (by fun_prop)]
  exact Measure.map_id

-- The two errors are the same draw. Check distinct times in reverse chronological order,
-- including the negative slope denominator, and check both conclusions at a repeated time.
example :
    let Q := linearDegradationLaw sharedNoise 4 2 (5, 3)
    let m₁ := ∫ y : ℝ × ℝ, y.1 ∂Q
    let m₂ := ∫ y : ℝ × ℝ, y.2 ∂Q
    Function.Injective (linearDegradationLaw sharedNoise 4 2) ∧
      (m₂ - m₁) / (2 - 4) = 3 ∧ m₁ - 4 * ((m₂ - m₁) / (2 - 4)) = 5 ∧
      linearDegradationLaw sharedNoise 2 2 (0, 0) = linearDegradationLaw sharedNoise 2 2 (-2, 1) ∧
      ¬ Function.Injective (linearDegradationLaw sharedNoise 2 2) := by
  have hIdent (t₁ t₂ : ℝ) := linearDegradation_identifiability sharedNoise
    (sharedNoise_fst.memLp (memLp_id_gaussianReal 2))
    (sharedNoise_snd.memLp (memLp_id_gaussianReal 2))
    (sharedNoise_fst.integral_eq.trans integral_id_gaussianReal)
    (sharedNoise_snd.integral_eq.trans integral_id_gaussianReal) t₁ t₂
  have hne : (4 : ℝ) ≠ 2 := by norm_num
  have h := (hIdent 4 2).2.1 hne (5, 3)
  exact ⟨(hIdent 4 2).1.mpr hne, h.1.symm, h.2.symm, (hIdent 2 2).2.2,
    fun hi => (hIdent 2 2).1.mp hi rfl⟩

-- A common additive bias can hide an intercept shift even at distinct times.
example : linearDegradationLaw (sharedNoise.map fun e : ℝ × ℝ => (e.1 + 2, e.2 + 2)) 4 2 (3, 3) =
    linearDegradationLaw sharedNoise 4 2 (5, 3) := by
  have h := linearDegradationLaw_shift_noise sharedNoise 4 2 (5, 3) 2
  norm_num at h
  exact h
