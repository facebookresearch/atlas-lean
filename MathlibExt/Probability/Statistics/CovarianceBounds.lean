/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Covariance bounds

General inequalities for covariance and variance of square-integrable
real random variables.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics

/-- `2 |Cov(X, Y)| ≤ Var X + Var Y` for square-integrable `X`, `Y`. -/
theorem two_mul_abs_covariance_le {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) : 2 * |cov[X, Y; μ]| ≤ Var[X; μ] + Var[Y; μ] := by
  have hXX := covariance_self (μ := μ) hX.aestronglyMeasurable.aemeasurable
  have hYY := covariance_self (μ := μ) hY.aestronglyMeasurable.aemeasurable
  have hYX := covariance_comm (μ := μ) Y X
  have hp : 0 ≤ Var[X + Y; μ] := variance_nonneg _ _
  have hm : 0 ≤ Var[X - Y; μ] := variance_nonneg _ _
  rw [← covariance_self (hX.add hY).aestronglyMeasurable.aemeasurable,
    covariance_add_left hX hY (hX.add hY), covariance_add_right hX hX hY,
    covariance_add_right hY hX hY] at hp
  rw [← covariance_self (hX.sub hY).aestronglyMeasurable.aemeasurable,
    covariance_sub_left hX hY (hX.sub hY), covariance_sub_right hX hX hY,
    covariance_sub_right hY hX hY] at hm
  rcases abs_cases (cov[X, Y; μ]) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith

end MathlibExt.Probability.Statistics
