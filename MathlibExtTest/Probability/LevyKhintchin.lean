/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LevyKhintchin

import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tests for the shared infinite-divisibility characterization

The standard Gaussian supplies a positive witness; the fair Bernoulli law supplies a negative
case. Both use `Measure.IsInfinitelyDivisible` through the existing Lévy-Khintchin theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory NNReal

namespace MathlibExtTest.Probability.LevyKhintchin

-- The standard Gaussian has convolution roots of every positive order.
example : Measure.IsInfinitelyDivisible (gaussianReal 0 1) := by
  apply (MetaMathlibExt.levy_Khintchin (gaussianReal 0 1) inferInstance).2
  refine ⟨0, 1, by norm_num, 0, by simp, by simp, fun t ↦ ?_⟩
  rw [charFun_gaussianReal]
  simp

-- An infinitely divisible probability measure on ℝ has a nowhere-zero characteristic function.
example (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hID : Measure.IsInfinitelyDivisible μ)
    (t : ℝ) :
    charFun μ t ≠ 0 := by
  obtain ⟨_, _, _, _, _, _, hchar⟩ :=
    (MetaMathlibExt.levy_Khintchin μ inferInstance).1 hID
  rw [hchar t]
  exact Complex.exp_ne_zero _

-- The fair Bernoulli law is not infinitely divisible because its characteristic function vanishes.
example :
    ¬ Measure.IsInfinitelyDivisible
      ((1 / 2 : ℝ≥0∞) • (Measure.dirac (0 : ℝ) + Measure.dirac 1)) := by
  let μ : Measure ℝ := (1 / 2 : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1)
  change ¬ Measure.IsInfinitelyDivisible μ
  intro hID
  have hprob : IsProbabilityMeasure μ := by
    dsimp only [μ]
    rw [isProbabilityMeasure_iff, Measure.smul_apply, Measure.add_apply]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hne : charFun μ Real.pi ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, hchar⟩ :=
      (MetaMathlibExt.levy_Khintchin μ hprob).1 hID
    rw [hchar Real.pi]
    exact Complex.exp_ne_zero _
  apply hne
  dsimp only [μ]
  rw [charFun_apply_real, integral_smul_measure]
  rw [integral_add_measure]
  · rw [integral_dirac, integral_dirac]
    norm_num
  · exact integrable_dirac (by simp)
  · exact integrable_dirac (by simp)

end MathlibExtTest.Probability.LevyKhintchin
