/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Probability.Statistics.EstimationRisk

import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ENNReal

/-!
# Finite mean squared error: variance plus squared bias

For normalized real weights on a finite type, `E[(X - θ)²] = Var X +
(E X - θ)²` (`expectation_sq_sub_eq_variance_add_sq`). Only the
normalization `∑ x, p x = 1` is used: the identity is algebraic and
needs no nonnegativity of `p` (the statistical reading, e.g.
`variance_le_expectation_sq_sub`, does). Without normalization the
identity fails.

The bridge theorems identify the finite quantities with the
measure-theoretic ones for a `PMF` law: `meanSquaredError` and `bias`
of `EstimationRisk` at `q.toMeasure` are the finite expectation and the
finite mean deviation, and the finite identity is the finite case of
`EstimationRisk.meanSquaredError_eq_variance_add_sq_bias`.
-/


namespace MathlibExt.Probability.FiniteProbability

/-- Finite mean squared error equals variance plus squared bias: for normalized real
weights `p` on a finite type, `E[(X - θ)²] = Var X + (E X - θ)²`. Only the normalization
`∑ x, p x = 1` is used; nonnegativity of `p` is not needed for the identity. -/
theorem expectation_sq_sub_eq_variance_add_sq {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∑ x, p x = 1) (X : α → ℝ) (θ : ℝ) :
    expectation p (fun x => (X x - θ) ^ 2) = variance p X + (expectation p X - θ) ^ 2 := by
  have hexpand : (fun x => (X x - θ) ^ 2) = fun x => X x ^ 2 - 2 * θ * X x + θ ^ 2 := by
    ext x; ring
  rw [hexpand, expectation_add, expectation_sub, expectation_const_mul, expectation_const hp,
    variance_eq_sub hp]
  ring

/-- For an estimator whose finite expectation is the target, the finite mean squared
error is the variance. -/
theorem expectation_sq_sub_eq_variance_of_expectation_eq {α : Type*} [Fintype α]
    {p : α → ℝ} (hp : ∑ x, p x = 1) {X : α → ℝ} {θ : ℝ} (hX : expectation p X = θ) :
    expectation p (fun x => (X x - θ) ^ 2) = variance p X := by
  have h := expectation_sq_sub_eq_variance_add_sq hp X θ
  rw [hX, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at h
  exact h

/-- The finite mean squared error at any target is at least the variance: the mean
minimizes expected squared error. Uses the normalization only. -/
theorem variance_le_expectation_sq_sub {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∑ x, p x = 1) (X : α → ℝ) (θ : ℝ) :
    variance p X ≤ expectation p (fun x => (X x - θ) ^ 2) := by
  have h := expectation_sq_sub_eq_variance_add_sq hp X θ
  have hnn : 0 ≤ (expectation p X - θ) ^ 2 := sq_nonneg _
  linarith

/-- Bridge: the source finite MSE of `EstimationRisk` under the law `q.toMeasure` of a
probability mass function on a finite type is the finite-weight expected squared error
for the real weights `(q a).toReal`. -/
theorem meanSquaredError_toMeasure_eq_expectation {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (q : PMF α) (X : α → ℝ) (θ : ℝ) :
    Statistics.EstimationRisk.meanSquaredError X q.toMeasure.toProbabilityMeasure θ
        Integrable.of_finite =
      expectation (fun a => (q a).toReal) (fun a => (X a - θ) ^ 2) := by
  rw [Statistics.EstimationRisk.meanSquaredError_eq_integral, Measure.coe_toProbabilityMeasure,
    integral_toMeasure_eq_expectation]

/-- Bridge: the source finite bias of `EstimationRisk` under `q.toMeasure` is the
finite-weight expectation minus the target. -/
theorem bias_toMeasure_eq_expectation_sub {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (q : PMF α) (X : α → ℝ) (θ : ℝ) :
    Statistics.EstimationRisk.bias X q.toMeasure.toProbabilityMeasure θ Integrable.of_finite =
      expectation (fun a => (q a).toReal) X - θ := by
  rw [Statistics.EstimationRisk.bias_eq_integral, Measure.coe_toProbabilityMeasure,
    integral_toMeasure_eq_expectation]

/-- Agreement of the finite and square-integrable identities: for a probability mass
function on a finite type, the finite-weight expected squared error equals the
measure-theoretic variance plus the squared `EstimationRisk` bias under `q.toMeasure`,
which is the conclusion of `meanSquaredError_eq_variance_add_sq_bias` for that law. -/
theorem expectation_sq_sub_eq_variance_toMeasure_add_sq_bias {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (q : PMF α) (X : α → ℝ) (θ : ℝ) :
    expectation (fun a => (q a).toReal) (fun a => (X a - θ) ^ 2) =
      ProbabilityTheory.variance X q.toMeasure +
        (Statistics.EstimationRisk.bias X q.toMeasure.toProbabilityMeasure θ
          Integrable.of_finite) ^ 2 := by
  rw [expectation_sq_sub_eq_variance_add_sq (sum_toReal_eq_one q),
    variance_toMeasure_eq, bias_toMeasure_eq_expectation_sub]

end MathlibExt.Probability.FiniteProbability
