/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CauchySelfNormalizedBoundAIMProbabilityProblem23

/-!
# Tests for the time-uniform self-normalized bound for Cauchy sums

The bound never exceeds `1`, and at `m = 0` it equals `1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.CauchySelfNormalizedBoundAIMProbabilityProblem23Wanted

namespace MathlibExtTest.Probability.CauchySelfNormalizedBoundAIMProbabilityProblem23

/-- The Cauchy self-normalized bound never exceeds `1`, since `-2 m x² ≤ 0`. -/
example (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X)
    (hlaw : ∀ i, volume.map (X i) = cauchyMeasure 0 1) (m x : ℝ) (hm : 0 ≤ m)
    (hx : 0 ≤ x) :
    volume {ω | ∃ t : ℕ,
      x < (∑ i ∈ Finset.range t, X i ω) / (∑ i ∈ Finset.range t, X i ω ^ 2 + m)} ≤ 1 := by
  refine le_trans (cauchySelfNormalizedBound_holds Ω X hmeas hindep hlaw m x hm hx) ?_
  have hnonneg : (0 : ℝ) ≤ 2 * m * x ^ 2 :=
    mul_nonneg (mul_nonneg zero_le_two hm) (sq_nonneg x)
  have hexp : Real.exp (-2 * m * x ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [hnonneg]
  calc ENNReal.ofReal (Real.exp (-2 * m * x ^ 2)) ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal hexp
    _ = 1 := ENNReal.ofReal_one

/-- At `m = 0`, the Cauchy self-normalized bound equals `1`. -/
example (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X)
    (hlaw : ∀ i, volume.map (X i) = cauchyMeasure 0 1) (x : ℝ) (hx : 0 ≤ x) :
    volume {ω | ∃ t : ℕ,
      x < (∑ i ∈ Finset.range t, X i ω) / (∑ i ∈ Finset.range t, X i ω ^ 2 + 0)} ≤ 1 := by
  have h := cauchySelfNormalizedBound_holds Ω X hmeas hindep hlaw 0 x le_rfl hx
  rw [show (-2 : ℝ) * 0 * x ^ 2 = 0 by ring, Real.exp_zero, ENNReal.ofReal_one] at h
  exact h

end MathlibExtTest.Probability.CauchySelfNormalizedBoundAIMProbabilityProblem23
