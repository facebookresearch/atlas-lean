/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CdfContinuityPoints
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open MathlibExt.Probability.CdfContinuityPoints

namespace MathlibExtTest.Probability.CdfContinuityPoints

/-- Signature restatement: atom-jump formula for the cdf. -/
theorem measure_singleton_eq_cdf_sub_leftLim_test
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    μ {x} = ENNReal.ofReal (cdf μ x - Function.leftLim (cdf μ) x) :=
  measure_singleton_eq_cdf_sub_leftLim μ x

/-- Signature restatement: continuity of the cdf iff no atom. -/
theorem continuousAt_cdf_iff_measure_singleton_eq_zero_test
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ContinuousAt (cdf μ) x ↔ μ {x} = 0 :=
  continuousAt_cdf_iff_measure_singleton_eq_zero μ x

/-- Signature restatement: continuity of the cdf kills the singleton. -/
theorem cdf_continuousAt_singleton_null_test
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ)
    (hx : ContinuousAt (cdf μ) x) :
    μ {x} = 0 :=
  cdf_continuousAt_singleton_null μ x hx

/-- Signature restatement: continuity of the cdf kills the frontier of `Iic x`. -/
theorem cdf_continuousAt_frontier_Iic_null_test
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ)
    (hx : ContinuousAt (cdf μ) x) :
    μ (frontier (Iic x)) = 0 :=
  cdf_continuousAt_frontier_Iic_null μ x hx

/-- Signature restatement: mass of `(a, b]` from the cdf. -/
theorem measure_Ioc_eq_ofReal_cdf_test
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ) :
    μ (Ioc a b) = ENNReal.ofReal (cdf μ b - cdf μ a) :=
  measure_Ioc_eq_ofReal_cdf μ a b

/-- Signature restatement: continuity points of the cdf are dense. -/
theorem dense_cdf_continuityPoints_test (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Dense {x : ℝ | ContinuousAt (cdf μ) x} :=
  dense_cdf_continuityPoints μ

/-- The Dirac mass at `0` has an atom at `0`, so its cdf is discontinuous
at `0`. -/
theorem not_continuousAt_cdf_dirac_zero :
    ¬ ContinuousAt (cdf (Measure.dirac (0 : ℝ))) 0 := by
  rw [continuousAt_cdf_iff_measure_singleton_eq_zero]
  simp

/-- The Dirac mass at `0` has no atom at `1`, so its cdf is continuous
at `1`. -/
theorem continuousAt_cdf_dirac_at_one :
    ContinuousAt (cdf (Measure.dirac (0 : ℝ))) 1 := by
  rw [continuousAt_cdf_iff_measure_singleton_eq_zero]
  simp

/-- The Dirac mass at `0` assigns mass `1` to `(-1, 1]`, which the cdf
formula recovers as `F(1) - F(-1) = 1 - 0`. -/
theorem measure_Ioc_dirac_zero :
    Measure.dirac (0 : ℝ) (Ioc (-1 : ℝ) 1) = 1 := by
  rw [measure_Ioc_eq_ofReal_cdf, cdf_eq_real, cdf_eq_real]
  simp [Measure.real]

/-- The standard Gaussian has no atoms, so its cdf is continuous at
every point. -/
theorem continuousAt_cdf_gaussianReal (x : ℝ) :
    ContinuousAt (cdf (gaussianReal 0 (1 : ℝ≥0))) x := by
  rw [continuousAt_cdf_iff_measure_singleton_eq_zero]
  have : NullSingletonClass (gaussianReal 0 (1 : ℝ≥0)) :=
    nullSingletonClass_gaussianReal (by norm_num)
  exact measure_singleton x

/-- There is a continuity point of the Dirac cdf in `(-1, 1)` (indeed
every point except `0` is one, but this exercises density). -/
theorem exists_continuity_point_dirac :
    ∃ x ∈ Ioo (-1 : ℝ) 1, ContinuousAt (cdf (Measure.dirac (0 : ℝ))) x := by
  obtain ⟨x, hx_mem, hx_cont⟩ :=
    (dense_cdf_continuityPoints (Measure.dirac (0 : ℝ))).inter_open_nonempty
      (Ioo (-1 : ℝ) 1) isOpen_Ioo ⟨(0 : ℝ), by norm_num⟩
  exact ⟨x, hx_mem, hx_cont⟩

#print axioms continuousAt_cdf_gaussianReal

end MathlibExtTest.Probability.CdfContinuityPoints
