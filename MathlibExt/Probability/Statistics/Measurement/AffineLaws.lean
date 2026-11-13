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
transform affinely and variances quadratically under `x ↦ a * x + b`. Two
purely algebraic lemmas hold for every nonzero slope `a`, including the
order-reversing `a < 0`: ratios of differences are invariant, and ratios of
values are invariant on inputs with nonzero denominators exactly when `b = 0`.
Admissible recodings of a measurement scale preserve order, so they have
`0 < a`; `ratioScale_admissible_iff` shows that an affine recoding is strictly
increasing and preserves ratios of values exactly when it is a positive
similarity (`0 < a` and `b = 0`). Main results:
`MeasureTheory.integral_const_mul_add_const`,
`ProbabilityTheory.variance_const_mul_add_const`, `affine_sub_div_affine_sub`,
`forall_affine_div_affine_eq_div_iff` and `ratioScale_admissible_iff`.

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

/-- Purely algebraic: ratios of differences are invariant under `x ↦ a * x + b`
for every nonzero slope, including the order-reversing `a < 0`, on inputs with
nonzero denominator `z - w`. The admissible interval-scale recodings are the
increasing ones (`0 < a`), a special case. -/
theorem affine_sub_div_affine_sub {a b : ℝ} (ha : a ≠ 0)
    (x y z w : ℝ) (hz : z - w ≠ 0) :
    (a * x + b - (a * y + b)) / (a * z + b - (a * w + b)) =
      (x - y) / (z - w) := by
  have h1 : a * x + b - (a * y + b) = a * (x - y) := by ring
  have h2 : a * z + b - (a * w + b) = a * (z - w) := by ring
  rw [h1, h2]
  have haz : a * (z - w) ≠ 0 := mul_ne_zero ha hz
  exact mul_div_mul_left _ _ ha

/-- Purely algebraic: for a nonzero slope `a` of either sign, ratios of values
are invariant on inputs with nonzero denominators (`y ≠ 0` and
`a * y + b ≠ 0`) iff `b = 0`. A negative slope reverses order and is not an
admissible scale transformation; `ratioScale_admissible_iff` is the
measurement-scale statement. -/
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

/-- **Admissible ratio-scale recodings** (Stevens 1946): an affine recoding
`x ↦ a * x + b` is strictly increasing and preserves ratios of values on inputs
with nonzero denominators exactly when it is a positive similarity, `0 < a` and
`b = 0`. The order-reversing similarity `x ↦ -x` preserves ratios but is
excluded. -/
theorem ratioScale_admissible_iff {a b : ℝ} :
    (StrictMono (fun x : ℝ => a * x + b) ∧
      ∀ x y : ℝ, y ≠ 0 → a * y + b ≠ 0 → (a * x + b) / (a * y + b) = x / y) ↔
      0 < a ∧ b = 0 := by
  constructor
  · rintro ⟨hmono, hratio⟩
    have h01 : a * 0 + b < a * 1 + b := hmono (by norm_num : (0 : ℝ) < 1)
    have ha : 0 < a := by linarith
    exact ⟨ha, (forall_affine_div_affine_eq_div_iff ha.ne').mp hratio⟩
  · rintro ⟨ha, rfl⟩
    refine ⟨fun x y hxy => ?_, (forall_affine_div_affine_eq_div_iff ha.ne').mpr rfl⟩
    change a * x + 0 < a * y + 0
    linarith [mul_lt_mul_of_pos_left hxy ha]

end MathlibExt.Probability.Statistics.Measurement
