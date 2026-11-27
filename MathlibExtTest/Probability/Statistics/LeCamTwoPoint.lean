/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LeCamTwoPoint

@[expose] public section

/-!
# Tests for Le Cam's two-point method

With the 0-1 loss on `Bool` (which satisfies the triangle inequality with `α = 1`) and a model
that does not depend on the parameter, the minimax risk over randomised estimators is at least
`1/2`: the bound `1 · (1 - 0) ≤ 2 · minimaxRisk`. Random guessing attains `1/2`, so the bound is
tight here (Polyanskiy and Wu, Remark 28.4); every deterministic estimator has risk `1`.
-/

open MeasureTheory ProbabilityTheory ENNReal
open MathlibExt.Probability.TotalVariationDistance MathlibExt.Probability.Statistics.LeCamTwoPoint

namespace MathlibExtTest.Probability.Statistics.LeCamTwoPoint

/-- The 0-1 loss on `Bool`. -/
def zeroOne (a b : Bool) : ℝ≥0∞ := if a = b then 0 else 1

lemma zeroOne_tri (a b t : Bool) : zeroOne a b ≤ 1 * (zeroOne a t + zeroOne b t) := by
  cases a <;> cases b <;> cases t <;> simp [zeroOne]

lemma measurable_zeroOne (a : Bool) : Measurable (zeroOne a) := measurable_of_countable _

/-- An uninformative model: the minimax 0-1 risk over randomised estimators is at least `1/2`. -/
example {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
    1 ≤ 2 * minimaxRisk zeroOne (Kernel.const Bool ρ) := by
  have h := mul_one_sub_totalVariationDist_le_minimax (Kernel.const Bool ρ) zeroOne
    measurable_zeroOne 1 ENNReal.one_ne_top zeroOne_tri true false
  simpa [zeroOne, totalVariationDist_self] using h

end MathlibExtTest.Probability.Statistics.LeCamTwoPoint
