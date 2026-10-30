/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CharFunTaylorBounds

@[expose] public section

open MeasureTheory Filter Complex
open MathlibExt.Probability.CharFunTaylorBounds

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Signature restatement: second-order pointwise bound. -/
theorem norm_exp_ofReal_mul_I_sub_one_sub_le_test (u : ℝ) :
    ‖Complex.exp (↑u * Complex.I) - 1 - ↑u * Complex.I‖ ≤ u ^ 2 :=
  norm_exp_ofReal_mul_I_sub_one_sub_le u

/-- Signature restatement: second-order characteristic-function bound. -/
theorem norm_charFun_sub_one_sub_le_test (X : Ω → ℝ) (hmeas : Measurable X)
    (hX_sq_int : Integrable (fun ω => (X ω) ^ 2) μ)
    (t : ℝ) :
    ‖charFun (μ.map X) t - 1 - ↑t * Complex.I * ↑(∫ ω, X ω ∂μ)‖
      ≤ t ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ :=
  norm_charFun_sub_one_sub_le X hmeas hX_sq_int t

/-- Signature restatement: first-order characteristic-function bound. -/
theorem norm_charFun_sub_one_le_test (X : Ω → ℝ) (hmeas : Measurable X)
    (hX_int : Integrable (fun ω => |X ω|) μ) (t : ℝ) :
    ‖charFun (μ.map X) t - 1‖ ≤ |t| * ∫ ω, |X ω| ∂μ :=
  norm_charFun_sub_one_le X hmeas hX_int t

/-- Signature restatement: mean-zero characteristic-function bound. -/
theorem norm_charFun_sub_one_le_sq_mul_variance_test (X : Ω → ℝ)
    (hmeas : Measurable X) (hmean : ∫ ω, X ω ∂μ = 0)
    (hint2 : Integrable (fun ω => (X ω) ^ 2) μ) (t : ℝ) :
    ‖charFun (μ.map X) t - 1‖ ≤ t ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ :=
  norm_charFun_sub_one_le_sq_mul_variance X hmeas hmean hint2 t

/-- The zero random variable satisfies every hypothesis, and all the
bounds collapse to `0 ≤ 0`. -/
theorem charFun_taylor_bounds_zero (t : ℝ) :
    ‖charFun (μ.map (fun _ => (0 : ℝ))) t - 1‖ ≤ t ^ 2 * ∫ ω, ((fun _ => (0 : ℝ)) ω) ^ 2 ∂μ := by
  have h := norm_charFun_sub_one_le_sq_mul_variance (μ := μ)
    (fun _ => (0 : ℝ)) measurable_const (by simp) (by simp) t
  exact h

/-- The pointwise second-order bound at `u = 1 / 2`, as a concrete
numerical instance. -/
theorem norm_exp_ofReal_mul_I_sub_one_sub_le_half :
    ‖Complex.exp (↑(1 / 2 : ℝ) * Complex.I) - 1 - ↑(1 / 2 : ℝ) * Complex.I‖
      ≤ (1 / 2 : ℝ) ^ 2 :=
  norm_exp_ofReal_mul_I_sub_one_sub_le (1 / 2)

#print axioms norm_charFun_sub_one_le_sq_mul_variance_test
#print axioms norm_charFun_sub_one_sub_le_test
#print axioms norm_charFun_sub_one_le_test
