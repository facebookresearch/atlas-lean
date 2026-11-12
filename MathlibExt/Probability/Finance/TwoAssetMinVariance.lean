/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.Covariance

/-!
# Unconstrained two-asset minimum-variance weight

For two assets with returns `R₁, R₂`, the portfolio with weight `w` on `R₁`
and `1 - w` on `R₂` has variance `w²σ₁² + 2w(1-w)σ₁₂ + (1-w)²σ₂²`. When
`Var(R₁ - R₂) > 0`, the unconstrained minimizer is the explicit weight
`w* = (σ₂² - σ₁₂) / Var(R₁ - R₂)`. No budget or target-return constraint is
imposed and `w*` need not lie in `[0, 1]`; short sales are allowed. This is
distinct from the constrained `n`-asset minimizer in
`MathlibExt.Probability.Finance.MeanVariancePortfolio`.

## Main results

* `twoAssetVariance`: variance of the two-asset portfolio at weight `w`.
* `minVarianceWeight`: the unconstrained minimum-variance weight formula.
* `minVarianceWeight_isMinimizer`: `w*` globally minimizes the variance.

Atlas roadmap target FI06.T01.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.TwoAssetMinVariance

/-- Variance of the two-asset portfolio with weight `w` on `R₁` and `1 - w`
on `R₂` (source clause: "portfolio return `w R₁ + (1 - w) R₂`"). Short sales
are allowed: `w` is unconstrained. -/
noncomputable def twoAssetVariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (R₁ R₂ : Ω → ℝ) (w : ℝ) : ℝ :=
  ProbabilityTheory.variance (fun ω => w * R₁ ω + (1 - w) * R₂ ω) μ

/-- The unconstrained two-asset minimum-variance weight
`(σ₂² - σ₁₂) / Var(R₁ - R₂)` (source clause: "w* = (σ₂² - σ₁₂) / Var(R₁-R₂)").
The denominator is `Var(R₁ - R₂) = σ₁² - 2σ₁₂ + σ₂²`. -/
noncomputable def minVarianceWeight {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (R₁ R₂ : Ω → ℝ) : ℝ :=
  (ProbabilityTheory.variance R₂ μ - ProbabilityTheory.covariance R₁ R₂ μ) /
    ProbabilityTheory.variance (fun ω => R₁ ω - R₂ ω) μ

/-- Quadratic expansion of the two-asset portfolio variance (proof-only
helper for `minVarianceWeight_isMinimizer`). -/
private theorem twoAssetVariance_quad {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {R₁ R₂ : Ω → ℝ} (hR₁ : MeasureTheory.MemLp R₁ 2 μ)
    (hR₂ : MeasureTheory.MemLp R₂ 2 μ) (w : ℝ) :
    twoAssetVariance μ R₁ R₂ w
      = w ^ 2 * ProbabilityTheory.variance R₁ μ
        + 2 * w * (1 - w) * ProbabilityTheory.covariance R₁ R₂ μ
        + (1 - w) ^ 2 * ProbabilityTheory.variance R₂ μ := by
  have h1 : MeasureTheory.MemLp (fun ω => w * R₁ ω) 2 μ := hR₁.const_mul w
  have h2 : MeasureTheory.MemLp (fun ω => (1 - w) * R₂ ω) 2 μ :=
    hR₂.const_mul (1 - w)
  have hsum : (fun ω => w * R₁ ω + (1 - w) * R₂ ω)
      = (fun ω => w * R₁ ω) + (fun ω => (1 - w) * R₂ ω) := rfl
  unfold twoAssetVariance
  rw [hsum, ProbabilityTheory.variance_add h1 h2,
    ProbabilityTheory.variance_const_mul, ProbabilityTheory.variance_const_mul,
    ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right]
  ring

/-- **The unconstrained two-asset minimum-variance weight.** When
`Var(R₁ - R₂) > 0`, the weight `w* = (σ₂² - σ₁₂) / Var(R₁ - R₂)` globally
minimizes the two-asset portfolio variance (Atlas roadmap FI06.T01). No
budget/target-return constraint is imposed; `w*` need not lie in `[0, 1]`. -/
theorem minVarianceWeight_isMinimizer {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {R₁ R₂ : Ω → ℝ} (hR₁ : MeasureTheory.MemLp R₁ 2 μ)
    (hR₂ : MeasureTheory.MemLp R₂ 2 μ)
    (hpos : 0 < ProbabilityTheory.variance (fun ω => R₁ ω - R₂ ω) μ) :
    ∀ w : ℝ, twoAssetVariance μ R₁ R₂ (minVarianceWeight μ R₁ R₂) ≤
      twoAssetVariance μ R₁ R₂ w := by
  intro w
  have hD : ProbabilityTheory.variance (fun ω => R₁ ω - R₂ ω) μ ≠ 0 :=
    ne_of_gt hpos
  have hsub : (fun ω => R₁ ω - R₂ ω) = R₁ - R₂ := rfl
  have hDexp : ProbabilityTheory.variance (fun ω => R₁ ω - R₂ ω) μ
      = ProbabilityTheory.variance R₁ μ - 2 * ProbabilityTheory.covariance R₁ R₂ μ
        + ProbabilityTheory.variance R₂ μ := by
    rw [hsub, ProbabilityTheory.variance_sub hR₁ hR₂]
  have hD' : ProbabilityTheory.variance R₁ μ - 2 * ProbabilityTheory.covariance R₁ R₂ μ
      + ProbabilityTheory.variance R₂ μ ≠ 0 := by
    rw [← hDexp]
    exact hD
  have key : twoAssetVariance μ R₁ R₂ w
      - twoAssetVariance μ R₁ R₂ (minVarianceWeight μ R₁ R₂)
      = ProbabilityTheory.variance (fun ω => R₁ ω - R₂ ω) μ
        * (w - minVarianceWeight μ R₁ R₂) ^ 2 := by
    rw [twoAssetVariance_quad hR₁ hR₂ w,
      twoAssetVariance_quad hR₁ hR₂ (minVarianceWeight μ R₁ R₂)]
    unfold minVarianceWeight
    rw [hDexp]
    field_simp [hD']
    ring
  have hnn : 0 ≤ ProbabilityTheory.variance (fun ω => R₁ ω - R₂ ω) μ
      * (w - minVarianceWeight μ R₁ R₂) ^ 2 :=
    mul_nonneg (le_of_lt hpos) (sq_nonneg _)
  linarith

end MathlibExt.Probability.Finance.TwoAssetMinVariance
