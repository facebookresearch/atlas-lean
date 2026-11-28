/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.NegativeBinomialMeasure

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace MathlibExtTest.Probability.Distributions.NegativeBinomialMeasure

/-- With size `1` and mean `1` the law is geometric: `P(0) = 1 / 2` and `P(1) = 1 / 4`. -/
example :
    (negBinomialMeasure 1 1).real {0} = 1 / 2 ∧ (negBinomialMeasure 1 1).real {1} = 1 / 4 := by
  rw [negBinomialMeasure_real_singleton one_pos zero_le_one,
    negBinomialMeasure_real_singleton one_pos zero_le_one]
  constructor <;> norm_num [negBinomialReal]

/-- The masses are those of `negBinomialReal`: `NB(2, 2)` has `P(0) = P(1) = 1 / 4`. -/
example : negBinomialMeasure 2 2 {0} = ENNReal.ofReal (1 / 4) ∧
    negBinomialMeasure 2 2 {1} = ENNReal.ofReal (1 / 4) := by
  simp only [negBinomialMeasure_singleton]
  refine ⟨?_, ?_⟩ <;> congr 1 <;>
    norm_num [negBinomialReal, ascPochhammer_one, show (2 : ℝ) = (2 : ℕ) by norm_num,
      Real.rpow_natCast]

/-- Mean `0` gives the point mass at `0`. -/
example (k : ℕ) (hk : k ≠ 0) : negBinomialMeasure 2 0 {k} = 0 := by
  simp [negBinomialReal_mean_zero two_pos, hk]

/-- A probability measure with mean `μ` on the parameter domain. -/
example : IsProbabilityMeasure (negBinomialMeasure 2 3) ∧
    ∫ k, (k : ℝ) ∂negBinomialMeasure 2 3 = 3 :=
  ⟨isProbabilityMeasure_negBinomialMeasure two_pos (by norm_num),
    integral_negBinomialMeasure two_pos (by norm_num)⟩

/-- Outside the parameter domain a negative value of the formula is read as mass `0`: at `θ = 1`,
`μ = -1/2`, `NB(1; θ, μ) = 2 · (-1) = -2`. -/
example : negBinomialReal 1 (-1 / 2) 1 = -2 ∧ negBinomialMeasure 1 (-1 / 2) {1} = 0 := by
  have h : negBinomialReal 1 (-1 / 2) 1 = -2 := by norm_num [negBinomialReal]
  refine ⟨h, ?_⟩
  rw [negBinomialMeasure_singleton, h, ENNReal.ofReal_eq_zero]
  norm_num

end MathlibExtTest.Probability.Distributions.NegativeBinomialMeasure
