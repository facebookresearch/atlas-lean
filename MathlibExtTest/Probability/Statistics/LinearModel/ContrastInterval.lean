/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.ContrastInterval

/-!
# Tests for `MathlibExt.Probability.Statistics.LinearModel.ContrastInterval`

At `n = 2` the Cauchy (`t_1`) interval still covers; `n ≥ 2` gives positive degrees of
freedom; the universal set has full `t` mass.
-/

namespace ProbabilityTheory.OneSampleChecks

open MeasureTheory ProbabilityTheory Real

/-- Use case: at `n = 2` the Cauchy (`t_1`) interval still covers. -/
example (μ : ℝ) {v : NNReal} (hv : v ≠ 0) (c : ℝ) {α : ℝ}
    (hmass : (studentTMeasure ((2 : ℕ) - 1)).real (Set.Icc (-c) c) ≥ 1 - α)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin 2 → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin 2 => gaussianReal μ v) P) :
    1 - α ≤ P.real {ω | |(∑ i, X ω i) / 2 - μ| ≤ c *
      √((∑ i, (X ω i - (∑ j, X ω j) / 2) ^ 2) / (((2 : ℕ) : ℝ) - 1)) / √(2 : ℝ)} := by
  exact one_sample_t_interval_coverage (le_refl 2) μ hv c hmass hα hX

/-- Positive degrees of freedom: `n ≥ 2` gives a positive `df`. -/
example (n : ℕ) (hn : 2 ≤ n) : 0 < n - 1 := by
  omega
/-- Endpoint: the universal set has full `t` mass, so `alpha = 1` always works. -/
example (d : ℕ) (hd : 0 < d) : (studentTMeasure d).real Set.univ = 1 := by
  have := isProbabilityMeasure_studentTMeasure hd
  exact probReal_univ
end ProbabilityTheory.OneSampleChecks
