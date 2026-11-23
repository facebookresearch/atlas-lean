/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.AffineLaws
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Tests for linear linking (z-score equating)

Exercises the affine score map `F(x) = muY + (sigmaY/sigmaX) * (x - muX)`
and its reverse through the public affine laws: roundtrip identities,
mean transport and variance transport for positive scales, positive-scale
numeric values, and the zero-scale boundary (where the displayed Lean
expression collapses; no linking map is claimed there).
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement.LinearLinking

/-- Reverse after forward is the identity, for positive scales.
Pure real arithmetic: `R (F x) = x`. -/
theorem reverse_comp_forward (μX μY σX σY : ℝ) (hσX : 0 < σX) (hσY : 0 < σY)
    (x : ℝ) :
    μX + (σX / σY) * ((μY + (σY / σX) * (x - μX)) - μY) = x := by
  have hX : σX ≠ 0 := ne_of_gt hσX
  have hY : σY ≠ 0 := ne_of_gt hσY
  field_simp
  ring

/-- Forward after reverse is the identity, for positive scales.
Pure real arithmetic: `F (R y) = y`. -/
theorem forward_comp_reverse (μX μY σX σY : ℝ) (hσX : 0 < σX) (hσY : 0 < σY)
    (y : ℝ) :
    μY + (σY / σX) * ((μX + (σX / σY) * (y - μY)) - μX) = y := by
  have hX : σX ≠ 0 := ne_of_gt hσX
  have hY : σY ≠ 0 := ne_of_gt hσY
  field_simp
  ring

set_option linter.unusedVariables false in
/-- Mean transport: if `∫ X = μX` for a probability measure, then the
linked variable has integral `μY`.

Proved by writing the integrand as
`(σY / σX) * X ω + (μY - (σY / σX) * μX)` and applying the affine mean law. -/
theorem integral_linked_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} (μX μY σX σY : ℝ) (hσX : 0 < σX) (hσY : 0 < σY)
    (hX : MeasureTheory.Integrable X μ)
    (hmean : ∫ ω, X ω ∂μ = μX) :
    ∫ ω, (μY + (σY / σX) * (X ω - μX)) ∂μ = μY := by
  have heq : (fun ω => μY + (σY / σX) * (X ω - μX))
      = (fun ω => (σY / σX) * X ω + (μY - (σY / σX) * μX)) := by
    funext ω; ring
  rw [heq, MeasureTheory.integral_const_mul_add_const hX, hmean]
  ring

/-- Variance transport: if `variance X μ = σX ^ 2`, then the linked
variable has variance `σY ^ 2`.

No mean hypothesis is needed: the shift is absorbed by the constant term
of the affine variance law. -/
theorem variance_linked_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} (μX μY σX σY : ℝ) (hσX : 0 < σX) (hσY : 0 < σY)
    (hX : MeasureTheory.AEStronglyMeasurable X μ)
    (hvar : ProbabilityTheory.variance X μ = σX ^ 2) :
    ProbabilityTheory.variance
        (fun ω => μY + (σY / σX) * (X ω - μX)) μ = σY ^ 2 := by
  have hXne : σX ≠ 0 := ne_of_gt hσX
  have heq : (fun ω => μY + (σY / σX) * (X ω - μX))
      = (fun ω => (σY / σX) * X ω + (μY - (σY / σX) * μX)) := by
    funext ω; ring
  rw [heq, ProbabilityTheory.variance_const_mul_add_const hX, hvar]
  field_simp

/-- Nonvacuity, positive scale, forward value: with `μX = 10`, `σX = 2`,
`μY = 50`, `σY = 15`, the score `x = 12` (one input SD above the input
mean) links to `65` (one target SD above the target mean). -/
theorem example_positive_scale_forward :
    (50 : ℝ) + ((15 : ℝ) / 2) * ((12 : ℝ) - 10) = 65 := by
  norm_num

/-- Nonvacuity, positive scale, roundtrip value: reversing `65` under the
same parameters returns `12`. -/
theorem example_positive_scale_reverse :
    (10 : ℝ) + ((2 : ℝ) / 15) * (((50 : ℝ) + ((15 : ℝ) / 2) * ((12 : ℝ) - 10)) - 50)
      = 12 := by
  norm_num

/-- Zero scale, Lean encoding: at `σX = 0` the displayed forward
expression collapses to the constant `μY`, because Lean division by zero
is `σY / 0 = 0`. This pins the encoding's behaviour only; mathematically
the linking map is undefined at `σX = 0` and no linking claim is made. -/
theorem zero_scale_forward_collapses (μX μY σY x : ℝ) :
    μY + (σY / (0 : ℝ)) * (x - μX) = μY := by
  simp

/-- Zero scale, roundtrip failure: the roundtrip identity of
`reverse_comp_forward` is false at `σX = 0` (here `σY = 1`,
`μX = μY = 0`, `x = 1`): the left side is `0`, not `1`. -/
theorem zero_scale_roundtrip_counterexample :
    (0 : ℝ) + ((0 : ℝ) / 1) * (((0 : ℝ) + (1 / (0 : ℝ)) * ((1 : ℝ) - 0)) - 0)
      ≠ 1 := by
  simp

end MathlibExtTest.Probability.Statistics.Measurement.LinearLinking
