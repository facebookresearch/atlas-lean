/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Process.Girsanov

/-! # Tests for Girsanov's theorem for a constant drift -/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MathlibExt.Probability.GirsanovWanted.IsBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

-- The empty observation vector still detects the total mass of the tilted measure.
example (hB : IsBrownianReal B P) (μ : ℝ) (T : ℝ≥0) :
    IsProbabilityMeasure
      (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (μ * B T ω - μ ^ 2 * T / 2))) :=
  (hasLaw_sub_drift_withDensity hB μ T ∅ (by simp)).isProbabilityMeasure

-- Observing the endpoint gives the centered Gaussian, including the Dirac law at T = 0.
example (hB : IsBrownianReal B P) (μ : ℝ) (T : ℝ≥0) :
    HasLaw (fun ω ↦ B T ω - μ * T) (gaussianReal 0 T)
      (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (μ * B T ω - μ ^ 2 * T / 2))) := by
  have h := hasLaw_sub_drift_withDensity hB μ T {T} (by simp)
  exact (BrownianReal.measurePreserving_eval_projectiveFamily
    (I := {T}) ⟨T, Finset.mem_singleton_self T⟩).hasLaw.comp h
