/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescentPath

/-!
# Tests for the path-space moments of the two-locus coalescence times

The path-space theorems instantiated at complete linkage (`ρ = 0`, where `T_A = T_B` and
`E (T_A T_B) = E T_A² = 2`) and at `ρ = 1` (`E (T_A T_B) = 1 + 19/32`). The model is
non-vacuous: `twoLocusRate ρ` is a rate matrix for every `ρ ≥ 0`, so the step law is a
probability measure. Boundary: the closed form outside the domain, `ρ = -1`, would give a
covariance above `Var T_A = 1`; the path statements require `0 ≤ ρ`, which is what makes
`twoLocusRate ρ` a rate matrix.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent TwoLocusState
open MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescentPath
open scoped NNReal ENNReal

namespace MathlibExtTest.Biology.PopulationGenetics.TwoLocusCoalescentPath

variable [MeasurableSpace TwoLocusState] [DiscreteMeasurableSpace TwoLocusState]

/-- Non-vacuity: the law of the steps driving the chain is a probability measure. -/
example : IsProbabilityMeasure (ctmcInputMeasure (isRateMatrix_twoLocusRate (le_refl 0))) :=
  inferInstance

/-- Complete linkage: `E (T_A T_B) = 2`, the second moment of the common coalescence time. -/
example :
    ∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate 0) linked ω t) = true),
        (t : ℝ≥0∞)) *
      (⨅ (t : ℝ≥0) (_ : coalescedB (ctmcPath (twoLocusRate 0) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate (le_refl 0)) = 2 := by
  rw [lintegral_coalescenceTimeA_mul_coalescenceTimeB (le_refl 0), twoLocusCov_zero]
  norm_num

/-- At `ρ = 1`: `E (T_A T_B) = 1 + 19 / 32`. -/
example :
    ∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate 1) linked ω t) = true),
        (t : ℝ≥0∞)) *
      (⨅ (t : ℝ≥0) (_ : coalescedB (ctmcPath (twoLocusRate 1) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate zero_le_one) =
      ENNReal.ofReal (1 + 19 / 32) := by
  rw [lintegral_coalescenceTimeA_mul_coalescenceTimeB zero_le_one]
  norm_num [twoLocusCov, twoLocusDenom]

/-- At `ρ = 1`, the mean coalescence time at locus `A` is `1`. -/
example :
    ∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate 1) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate zero_le_one) = 1 :=
  lintegral_coalescenceTimeA zero_le_one

/-- The path-space covariance at `ρ = 1` is `19 / 32`. -/
example :
    (∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate 1) linked ω t) = true),
        (t : ℝ≥0∞)) *
      (⨅ (t : ℝ≥0) (_ : coalescedB (ctmcPath (twoLocusRate 1) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate zero_le_one)).toReal -
      (∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate 1) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate zero_le_one)).toReal *
      (∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedB (ctmcPath (twoLocusRate 1) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate zero_le_one)).toReal =
      19 / 32 := by
  rw [covariance_coalescenceTimes zero_le_one]
  norm_num [twoLocusCov, twoLocusDenom]

/-- Boundary: outside the domain the closed form exceeds `Var T_A = 1`
(`twoLocusCov (-1) = 17 / 6`); `twoLocusRate (-1)` has a negative off-diagonal rate. -/
example : twoLocusCov (-1) = 17 / 6 ∧ twoLocusRate (-1) linked partlySplit < 0 := by
  refine ⟨by norm_num [twoLocusCov, twoLocusDenom], ?_⟩
  simp [twoLocusRate]

#print axioms lintegral_coalescenceTimeA_mul_coalescenceTimeB

end MathlibExtTest.Biology.PopulationGenetics.TwoLocusCoalescentPath
