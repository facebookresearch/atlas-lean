/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ExponentialMoments

/-!
# Tests for moments of the exponential distribution

Concrete instances: mean, second moment and variance at rate `2`, the third moment at rate `1`,
the mean of a random variable with law `Exp 3`, and the integrability statements.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Distributions.ExponentialMoments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The identity and all powers are integrable against `Exp 2`. -/
example : Integrable id (expMeasure 2) ∧ Integrable (fun x : ℝ => x ^ 5) (expMeasure 2) :=
  ⟨integrable_id_expMeasure (by norm_num), integrable_pow_expMeasure (by norm_num) 5⟩

/-- A random variable with law `Exp 3` has variance `1/9`. -/
example {X : Ω → ℝ} (hX : HasLaw X (expMeasure 3) μ) : Integrable X μ ∧ Var[X; μ] = 1 / 9 := by
  refine ⟨hX.integrable_of_expMeasure (by norm_num), ?_⟩
  rw [hX.variance_eq_of_expMeasure (by norm_num)]
  norm_num

/-- Exponential law of rate `2`: mean `1/2`, second moment `1/2`, variance `1/4`. -/
example : ∫ x, x ∂(expMeasure 2) = 1 / 2 ∧ ∫ x, x ^ 2 ∂(expMeasure 2) = 1 / 2 ∧
    Var[id; expMeasure 2] = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_id_expMeasure (by norm_num)]
    norm_num
  · rw [integral_sq_expMeasure (by norm_num)]
    norm_num
  · rw [variance_id_expMeasure (by norm_num)]
    norm_num

/-- Third moment of `Exp 1` is `3! = 6`. -/
example : ∫ x, x ^ 3 ∂(expMeasure 1) = 6 := by
  rw [integral_pow_expMeasure one_pos]
  norm_num [Nat.factorial]

/-- A random variable with law `Exp 3` has mean `1/3`. -/
example {X : Ω → ℝ} (hX : HasLaw X (expMeasure 3) μ) : μ[X] = 1 / 3 := by
  rw [hX.integral_eq_inv_of_expMeasure (by norm_num)]
  norm_num

end MathlibExtTest.Probability.Distributions.ExponentialMoments
