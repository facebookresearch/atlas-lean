/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.DKWInequality
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.GlivenkoCantelliWanted
open MathlibExt.Probability.Statistics.DKWInequalityWanted
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.DKWInequality

private noncomputable def coinLaw : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 1

private instance coinLawProbability : IsProbabilityMeasure coinLaw where
  measure_univ := by simp [coinLaw, ENNReal.inv_two_add_inv_two]

private noncomputable def coinSamples : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ => coinLaw)

private instance coinSamplesProbability : IsProbabilityMeasure coinSamples := by
  unfold coinSamples
  infer_instance

private def sample (i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i

-- The law has atoms, and n = 0 represents one observation.
example {ε : ℝ} (hε : 0 < ε) :
    coinSamples {ω | ∃ x : ℝ, ε < |(empiricalCount sample 0 ω x : ℝ) -
        (coinLaw (Set.Iic x)).toReal|} ≤ ENNReal.ofReal (2 * Real.exp (-2 * ε ^ 2)) := by
  have hMeas (i : ℕ) : Measurable (sample i) := measurable_pi_apply i
  have hIndep : iIndepFun sample coinSamples :=
    iIndepFun_infinitePi (X := fun (_ : ℕ) (x : ℝ) => x) fun _ => measurable_id
  have hMap (i : ℕ) : coinSamples.map (sample i) = coinLaw :=
    Measure.infinitePi_map_eval (fun _ => coinLaw) i
  have hIdent (i : ℕ) : IdentDistrib (sample i) (sample 0) coinSamples coinSamples :=
    ⟨(hMeas i).aemeasurable, (hMeas 0).aemeasurable, (hMap i).trans (hMap 0).symm⟩
  have hCDF (x : ℝ) : coinSamples (sample 0 ⁻¹' Set.Iic x) = coinLaw (Set.Iic x) := by
    rw [← Measure.map_apply (hMeas 0) measurableSet_Iic, hMap]
  simpa [hCDF] using measure_exists_abs_empiricalCDF_sub_gt_le (P := coinSamples)
    sample hMeas hIndep hIdent (n := 0) (hε := hε)

end MathlibExtTest.Probability.Statistics.DKWInequality
