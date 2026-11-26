/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.BrownianHittingTime
import MathlibExt.Probability.BrownianMotionExistence
import MathlibExt.Probability.OrnsteinUhlenbeck

/-!
# Tests for the Brownian hitting-time law

Check the zero-time endpoint and the unit-level law on a continuous Brownian motion.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.BrownianHittingTime

open MathlibExt.Probability.BrownianStrongMarkovWanted.IsBrownianReal

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous fun t ↦ B t ω) {a : ℝ} (ha : 0 < a) :
    P {ω | B 0 ω = a} = 0 := by
  simpa using measure_hitting_le hB hc ha 0

example : ∃ (P : Measure (ℝ≥0 → ℝ)) (B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ), IsBrownianReal B P ∧
    P {ω | ∃ s ∈ Set.Icc (0 : ℝ≥0) 1, B s ω = 1} =
      ENNReal.ofReal (∫ s in (0 : ℝ)..1,
        1 / Real.sqrt (2 * Real.pi * s ^ 3) * Real.exp (-1 / (2 * s))) := by
  obtain ⟨P, hP⟩ := exists_isPreBrownianReal_eval
  have := hP.isGaussianProcess.isProbabilityMeasure
  obtain ⟨B, _, hc, _, hB⟩ := hP.exists_isBrownianReal_modification measurable_pi_apply
  exact ⟨P, B, hB, by simpa using measure_hitting_le hB hc zero_lt_one 1⟩

end MathlibExtTest.Probability.BrownianHittingTime
