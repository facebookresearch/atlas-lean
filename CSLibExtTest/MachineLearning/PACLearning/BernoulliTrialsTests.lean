/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.BernoulliTrials
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Bernoulli-trial bound tests

Instantiation with `h = 2`, `S = 1` and `m = 7` trials of success probability at least `1/2`
(the sample-size condition `2 · 2 · (1 + ln 2) ≤ 7` is discharged numerically): no success has
probability less than `1/2`. And the exponential moment at `-1` of a trial with success
probability `1/2` is `(1 + e⁻¹) / 2`.
-/

namespace Cslib.MachineLearning.PACLearning.BernoulliTrials

open MeasureTheory ProbabilityTheory Real

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 7 → Ω → ℝ) (hind : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (hp : ∀ i, 1 / 2 ≤ μ.real {ω | X i ω = 1}) :
    μ.real {ω | ∑ i, X i ω < (1 : ℕ)} < 1 / 2 := by
  refine measureReal_sum_lt_lt_inv X hind hmeas h01 (by norm_num) hp le_rfl ?_
  have := Real.log_two_lt_d9
  push_cast
  norm_num at this ⊢
  linarith

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) (hp : μ.real {ω | X ω = 1} = 1 / 2) :
    mgf X μ (-1) = (1 + exp (-1)) / 2 := by
  rw [mgf_neg_one_of_zero_or_one hX h01, hp]
  ring

end Cslib.MachineLearning.PACLearning.BernoulliTrials
