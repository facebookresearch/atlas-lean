/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Function.ConditionalExpectation.BestPredictor

/-!
# Tests for the conditional expectation as best predictor

* With the trivial σ-algebra: no constant beats the mean `E[Y]` in mean squared error.
* With features `X`: `E[Y | X]` beats every square-integrable `h ∘ X`.
-/

namespace MathlibExtTest.BestPredictor

open MeasureTheory

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : MemLp Y 2 μ) (c : ℝ) :
    ∫ ω, (Y ω - ∫ ω', Y ω' ∂μ) ^ 2 ∂μ ≤ ∫ ω, (Y ω - c) ^ 2 ∂μ := by
  simpa [condExp_bot] using
    integral_sq_sub_condExp_le bot_le hY (memLp_const c) stronglyMeasurable_const

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {Y X : Ω → ℝ}
    (hX : Measurable X) (hY : MemLp Y 2 μ) (hX2 : MemLp X 2 μ) :
    ∫ ω, (Y ω - μ[Y|MeasurableSpace.comap X inferInstance] ω) ^ 2 ∂μ ≤
      ∫ ω, (Y ω - 2 * X ω) ^ 2 ∂μ :=
  integral_sq_sub_condExp_comap_le hX hY (h := fun t => 2 * t) (by fun_prop)
    (hX2.const_mul 2)

end MathlibExtTest.BestPredictor
