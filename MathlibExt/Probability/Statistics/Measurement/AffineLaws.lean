/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Interval and ratio scales: affine laws for means, variances and ratios

This file formalizes the Stevens (1946) interval- and ratio-scale laws: means
transform affinely and variances quadratically under `x ↦ a * x + b`, ratios
of differences are invariant when `a ≠ 0`, and ratios of values are invariant
on admissible inputs (nonzero denominators) exactly for similarity maps
(`b = 0`). Main results: `MeasureTheory.integral_const_mul_add_const`,
`ProbabilityTheory.variance_const_mul_add_const`, `affine_sub_div_affine_sub`
and `forall_affine_div_affine_eq_div_iff`.

## References

* S. S. Stevens, *On the Theory of Scales of Measurement*,
  Science 103(2684) (7 June 1946), 677-680.
* R. V. Hogg, J. W. McKean and A. T. Craig, *Introduction to Mathematical
  Statistics*, 7th edition, Pearson, 2013, Theorem 1.9.1.
-/

@[expose] public section

namespace MeasureTheory

/-- Mean of an affine image: `∫ (a * X + b) = a * ∫ X + b`, for every `a`. -/
theorem integral_const_mul_add_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ} (hX : Integrable X μ) :
    ∫ ω, (a * X ω + b) ∂μ = a * ∫ ω, X ω ∂μ + b := by
  have h1 : Integrable (fun ω => a * X ω) μ :=
    Integrable.const_mul hX a
  have h2 : Integrable (fun _ : Ω => b) μ :=
    integrable_const b
  calc ∫ ω, (a * X ω + b) ∂μ
      = (∫ ω, a * X ω ∂μ) + ∫ _ : Ω, b ∂μ :=
        integral_add h1 h2
    _ = (a * ∫ ω, X ω ∂μ) + ∫ _ : Ω, b ∂μ := by
        rw [integral_const_mul]
    _ = (a * ∫ ω, X ω ∂μ) + μ.real Set.univ • b := by
        rw [integral_const]
    _ = a * ∫ ω, X ω ∂μ + b := by
        rw [probReal_univ, one_smul]

end MeasureTheory

namespace ProbabilityTheory

/-- Variance of an affine image: `Var[a * X + b] = a ^ 2 * Var[X]`.
Holds for every `a`. -/
theorem variance_const_mul_add_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hX : MeasureTheory.AEStronglyMeasurable X μ) :
    variance (fun ω => a * X ω + b) μ =
      a ^ 2 * variance X μ := by
  have hX' : MeasureTheory.AEStronglyMeasurable (fun ω => a * X ω) μ :=
    MeasureTheory.AEStronglyMeasurable.const_mul hX a
  calc variance (fun ω => a * X ω + b) μ
      = variance (fun ω => a * X ω) μ :=
        variance_add_const hX' b
    _ = a ^ 2 * variance X μ :=
        variance_const_mul a X μ

end ProbabilityTheory

namespace MathlibExt.Probability.Statistics.Measurement

/-- Ratios of differences are invariant under `x ↦ a * x + b` when `a ≠ 0`,
on admissible inputs (nonzero denominator `z - w`). -/
theorem affine_sub_div_affine_sub {a b : ℝ} (ha : a ≠ 0)
    (x y z w : ℝ) (hz : z - w ≠ 0) :
    (a * x + b - (a * y + b)) / (a * z + b - (a * w + b)) =
      (x - y) / (z - w) := by
  have h1 : a * x + b - (a * y + b) = a * (x - y) := by ring
  have h2 : a * z + b - (a * w + b) = a * (z - w) := by ring
  rw [h1, h2]
  have haz : a * (z - w) ≠ 0 := mul_ne_zero ha hz
  exact mul_div_mul_left _ _ ha

/-- Ratios of values are invariant on admissible inputs iff `b = 0`,
when `a ≠ 0`. Admissible means nonzero denominators: `y ≠ 0` and
`a * y + b ≠ 0`. -/
theorem forall_affine_div_affine_eq_div_iff {a b : ℝ} (ha : a ≠ 0) :
    (∀ x y : ℝ, y ≠ 0 → a * y + b ≠ 0 →
      (a * x + b) / (a * y + b) = x / y) ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    by_cases hab : a + b = 0
    · have hy : (2 : ℝ) ≠ 0 := by norm_num
      have heq : a * 2 + b = a + (a + b) := by ring
      have hden : a * 2 + b ≠ 0 := by
        rw [heq, hab, add_zero]
        exact ha
      have h42 := h 4 2 hy hden
      have h4div2 : (4 : ℝ) / 2 = 2 := by norm_num
      rw [h4div2] at h42
      have hmul : a * 4 + b = 2 * (a * 2 + b) :=
        (div_eq_iff hden).mp h42
      have hb0 : b = 0 := by linarith
      exact hb hb0
    · have hy : (1 : ℝ) ≠ 0 := by norm_num
      have heq1 : a * 1 + b = a + b := by ring
      have hden : a * 1 + b ≠ 0 := by
        rw [heq1]
        exact hab
      have h21 := h 2 1 hy hden
      have h2div1 : (2 : ℝ) / 1 = 2 := by norm_num
      rw [h2div1] at h21
      have hmul : a * 2 + b = 2 * (a * 1 + b) :=
        (div_eq_iff hden).mp h21
      have hb0 : b = 0 := by linarith
      exact hb hb0
  · intro hb x y _ _
    rw [hb, add_zero, add_zero]
    exact mul_div_mul_left _ _ ha

end MathlibExt.Probability.Statistics.Measurement
