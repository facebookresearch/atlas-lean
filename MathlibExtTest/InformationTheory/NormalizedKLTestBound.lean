/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.NormalizedKLTestBound

@[expose] public section

open MathlibExt.InformationTheory.NormalizedKLTestBound MeasureTheory InformationTheory
open scoped ENNReal

namespace MathlibExtTest.InformationTheory.NormalizedKLTestBound

/-- The zero score is normalized and gives `0 ≤ klDiv μ ν`. -/
example {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (∫ _ : α, (0 : ℝ) ∂μ) ≤ klDiv μ ν := by
  have h := integral_exp_zero_eq_one_and_ofReal_integral_zero_le_klDiv μ ν
  exact h.2

end MathlibExtTest.InformationTheory.NormalizedKLTestBound
