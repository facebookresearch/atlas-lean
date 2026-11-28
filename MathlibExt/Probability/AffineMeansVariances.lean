/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.AffineLaws

import Mathlib.Tactic.Ring

/-! # Means and variances under affine change of scale -/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MetaMathlibExt

@[expose] public section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Differences of means under a common affine map.** Applying the same affine map to two
integrable random variables on a probability space scales the difference of their means by the
slope. -/
theorem sub_means_affine [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) (a b : ℝ) :
    μ[fun ω => a * X ω + b] - μ[fun ω => a * Y ω + b] = a * (μ[X] - μ[Y]) := by
  rw [integral_const_mul_add_const hX, integral_const_mul_add_const hY]
  ring

/-- **Ratios of means under a common scaling.** Applying the same nonzero scaling preserves
the ratio of two Bochner integrals for any measure. A nonintegrable function has integral zero;
if the denominator is zero, both ratios are zero under the convention `x / 0 = 0`. -/
theorem div_means_const_mul {X Y : Ω → ℝ} {a : ℝ} (ha : a ≠ 0) :
    μ[fun ω => a * X ω] / μ[fun ω => a * Y ω] = μ[X] / μ[Y] := by
  simp only [integral_const_mul, mul_div_mul_left _ _ ha]

/-- **A ratio of means equal to one under an affine map.** On a probability space, a ratio of
Bochner integrals equal to one remains one under a common affine change if the transformed
denominator is nonzero. The original ratio being one forces both functions to be integrable
and both original integrals to be nonzero. The slope may be zero. -/
theorem div_means_affine_eq_one [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {a b : ℝ}
    (hFY₀ : μ[fun ω => a * Y ω + b] ≠ 0) (hratio : μ[X] / μ[Y] = 1) :
    μ[fun ω => a * X ω + b] / μ[fun ω => a * Y ω + b] = 1 := by
  have hY₀ : μ[Y] ≠ 0 := by
    intro hzero
    simp [hzero] at hratio
  have heq : μ[X] = μ[Y] := by simpa only [one_mul] using (div_eq_iff hY₀).mp hratio
  have hX : Integrable X μ := Integrable.of_integral_ne_zero (by rwa [heq])
  have hY : Integrable Y μ := Integrable.of_integral_ne_zero hY₀
  rw [integral_const_mul_add_const hX, integral_const_mul_add_const hY, heq, div_self]
  rwa [← integral_const_mul_add_const hY]

/-- **Ratios of differences of means under an affine map.** Applying the same affine map
with nonzero slope to four integrable random variables on a probability space preserves the
ratio of their mean differences. If the original denominator is zero, both ratios are zero
under the convention `x / 0 = 0`. -/
theorem div_sub_means_affine [IsProbabilityMeasure μ] {X Y U W : Ω → ℝ} {a b : ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) (hU : Integrable U μ) (hW : Integrable W μ)
    (ha : a ≠ 0) :
    (μ[fun ω => a * X ω + b] - μ[fun ω => a * Y ω + b]) /
      (μ[fun ω => a * U ω + b] - μ[fun ω => a * W ω + b]) = (μ[X] - μ[Y]) / (μ[U] - μ[W]) := by
  rw [sub_means_affine hX hY a b, sub_means_affine hU hW a b]
  exact mul_div_mul_left _ _ ha

/-- **Means and variances under affine change of scale.** Summary of the affine laws for
real random variables on an arbitrary probability space. The mean of an integrable variable
transforms affinely, and the variance of a square-integrable variable scales by the square
of the slope. Differences of means of integrable variables scale by the slope. For integrable
variables, ratios of means are invariant under nonzero scaling when the denominator is
nonzero. A ratio of one survives a common affine change when both the original and transformed
denominators are nonzero. Ratios of differences of means are invariant under a common affine
change with nonzero slope when the original denominator is nonzero.

For individual laws use `MeasureTheory.integral_const_mul_add_const`,
`ProbabilityTheory.variance_const_mul_add_const`, `sub_means_affine`, `div_means_const_mul`,
`div_means_affine_eq_one`, and `div_sub_means_affine`.

Grinstead and Snell, *Introduction to Probability*, Dartmouth PDF dated July 4, 2006,
Theorems 6.2 and 6.7 give the discrete expectation and variance cases. The formulation here
uses an arbitrary probability measure, and the statements on ratios follow algebraically. -/
theorem affine_mean_variance_laws (μ : Measure Ω) [IsProbabilityMeasure μ] (a b : ℝ) :
    (∀ {X : Ω → ℝ}, Integrable X μ → μ[fun ω => a * X ω + b] = a * μ[X] + b) ∧
    (∀ {X : Ω → ℝ}, MemLp X 2 μ → variance (fun ω => a * X ω + b) μ = a ^ 2 * variance X μ) ∧
    (∀ {X Y : Ω → ℝ}, Integrable X μ → Integrable Y μ →
      μ[fun ω => a * X ω + b] - μ[fun ω => a * Y ω + b] = a * (μ[X] - μ[Y])) ∧
    (∀ {X Y : Ω → ℝ}, Integrable X μ → Integrable Y μ → a ≠ 0 → μ[Y] ≠ 0 →
      μ[fun ω => a * X ω] / μ[fun ω => a * Y ω] = μ[X] / μ[Y]) ∧
    (∀ {X Y : Ω → ℝ}, Integrable X μ → Integrable Y μ →
      μ[Y] ≠ 0 → μ[fun ω => a * Y ω + b] ≠ 0 → μ[X] / μ[Y] = 1 →
      μ[fun ω => a * X ω + b] / μ[fun ω => a * Y ω + b] = 1) ∧
    (∀ {X Y U W : Ω → ℝ}, Integrable X μ → Integrable Y μ → Integrable U μ → Integrable W μ →
      a ≠ 0 → μ[U] - μ[W] ≠ 0 →
      (μ[fun ω => a * X ω + b] - μ[fun ω => a * Y ω + b]) /
        (μ[fun ω => a * U ω + b] - μ[fun ω => a * W ω + b]) = (μ[X] - μ[Y]) / (μ[U] - μ[W])) :=
  ⟨fun hX => integral_const_mul_add_const hX,
    fun hX => variance_const_mul_add_const hX.aestronglyMeasurable,
    fun hX hY => sub_means_affine hX hY a b,
    fun _ _ ha _ => div_means_const_mul ha,
    fun _ _ _ hFY₀ hratio => div_means_affine_eq_one hFY₀ hratio,
    fun hX hY hU hW ha _ => div_sub_means_affine hX hY hU hW ha⟩

end

end MetaMathlibExt
