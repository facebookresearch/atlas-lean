/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MeasurementErrorAttenuation

/-!
# Tests for measurement-error attenuation

Population attenuation at exact values (`Var X = 4`, `Var e = 1`, `β = 2`,
giving slope `8 / 5`), and the `sampleSlopeME` value at `n = 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.MeasurementErrorAttenuation

namespace MathlibExtTest.Probability.Statistics.MeasurementErrorAttenuation

/-- Population attenuation at exact values: `Var X = 4`, `Var e = 1`, `β = 2`
gives slope `2 * 4 / (4 + 1) = 8 / 5`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X e ε : Ω → ℝ} {α : ℝ}
    (hX : MemLp X 2 μ) (he : MemLp e 2 μ) (hε : MemLp ε 2 μ)
    (hXe : IndepFun X e μ) (hXε : IndepFun X ε μ) (heε : IndepFun e ε μ)
    (hW : variance (fun ω => X ω + e ω) μ ≠ 0)
    (hVX : variance X μ = 4) (hVe : variance e μ = 1) :
    covariance (fun ω => X ω + e ω) (fun ω => α + 2 * X ω + ε ω) μ /
      variance (fun ω => X ω + e ω) μ = 8 / 5 := by
  have h := measurementError_population_attenuation (α := α) (β := 2)
    hX he hε hXe hXε heε hW
  rw [hVX, hVe] at h
  norm_num at h
  exact h

/-- `sampleSlopeME` at `n = 1` is junk-but-well-defined (single centered term
is zero, so the ratio is `0 / _ = 0`). -/
example {Ω : Type*} (X e ε : ℕ → Ω → ℝ) (α β : ℝ) (ω : Ω) :
    sampleSlopeME X e ε α β 1 ω = 0 := by
  simp [sampleSlopeME, MathlibExt.Probability.FiniteProbability.olsSlope,
    MathlibExt.Probability.FiniteProbability.sxy,
    MathlibExt.Probability.FiniteProbability.sampleMean_eq_sum_div]


end MathlibExtTest.Probability.Statistics.MeasurementErrorAttenuation
