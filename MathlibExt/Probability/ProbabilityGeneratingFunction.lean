/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Probability generating functions

For a random variable `X : Ω → ℕ`, the probability generating function is
`pgf X μ s = E[s ^ X] = ∫ ω, s ^ X ω ∂μ`. It is an ordinary Bochner integral, so it is defined
for every real `s` and every measure. For a finite measure `μ` its guaranteed convergence domain
is `|s| ≤ 1`, where `s ^ X` is bounded by `1` (`integrable_pow_of_abs_le_one`); for an infinite
measure the integral can be the junk value `0` even there. The characteristic lemmas assume
`|s| ≤ 1` and a finite (or probability) measure wherever the value is meant as a mass.

## Main results

* `MathlibExt.Probability.pgf_eq_tsum`: on `|s| ≤ 1`, `pgf X μ s = ∑' k, s ^ k * P(X = k)`.
* `MathlibExt.Probability.pgf_add_of_indepFun`: the generating function of a sum of independent
  variables is the product of their generating functions.

Sources: Mathlib `docs/undergrad.yaml`, Probability Theory / Random variables and their laws /
probability generating functions; W. Feller, An Introduction to Probability Theory and Its
Applications, Vol. I, 3rd ed., Chapter XI.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probability generating function `G_X(s) = E[s ^ X]` of a random variable `X : Ω → ℕ`
under the measure `μ`. For a finite measure `μ` the integral converges on `|s| ≤ 1` (see
`integrable_pow_of_abs_le_one`); outside that domain, or for an infinite measure, the Bochner
integral may take the junk value `0`. -/
noncomputable def pgf (X : Ω → ℕ) (μ : Measure Ω) (s : ℝ) : ℝ :=
  ∫ ω, s ^ X ω ∂μ

theorem pgf_def (X : Ω → ℕ) (μ : Measure Ω) (s : ℝ) :
    pgf X μ s = ∫ ω, s ^ X ω ∂μ :=
  rfl

/-- On the convergence domain `|s| ≤ 1`, `s ^ X` is integrable for any measurable `X` under a
finite measure. -/
theorem integrable_pow_of_abs_le_one {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℕ}
    (hX : Measurable X) {s : ℝ} (hs : |s| ≤ 1) :
    Integrable (fun ω => s ^ X ω) μ := by
  have hpow : Measurable (fun k : ℕ => s ^ k) := measurable_from_nat
  exact Integrable.of_bound (hpow.comp hX).aestronglyMeasurable 1 <| ae_of_all _ fun ω => by
    simpa [Real.norm_eq_abs, abs_pow] using pow_le_one₀ (abs_nonneg s) hs

/-- Under a probability measure the generating function at `s = 1` is `1`. -/
@[simp]
theorem pgf_one (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] : pgf X μ 1 = 1 := by
  simp [pgf]

/-- The generating function at `s = 0` is `μ.real {ω | X ω = 0}`: the probability that `X = 0`
when `μ` is a probability measure, and the mass of that event when `μ` is finite. (For an infinite
measure both sides are computed with `ENNReal.toReal`, so the identity still holds but carries no
mass interpretation.) -/
theorem pgf_zero (X : Ω → ℕ) (μ : Measure Ω) (hX : Measurable X) :
    pgf X μ 0 = μ.real {ω | X ω = 0} := by
  have hfun : (fun ω => (0 : ℝ) ^ X ω) = Set.indicator (X ⁻¹' {0}) 1 := by
    funext ω
    by_cases h : X ω = 0 <;> simp [h, Set.indicator]
  rw [pgf, hfun, integral_indicator_one (hX (measurableSet_singleton 0))]
  rfl

/-- Series form of the generating function on its convergence domain: `G_X(s)` is the power
series with coefficients `P(X = k)`. -/
theorem pgf_eq_tsum (X : Ω → ℕ) (μ : Measure Ω) [IsFiniteMeasure μ] (hX : Measurable X)
    {s : ℝ} (hs : |s| ≤ 1) :
    pgf X μ s = ∑' k, s ^ k * μ.real {ω | X ω = k} := by
  have hpow : Measurable (fun k : ℕ => s ^ k) := measurable_from_nat
  have hint : Integrable (fun k : ℕ => s ^ k) (μ.map X) := by
    refine Integrable.of_bound hpow.aestronglyMeasurable 1 <| ae_of_all _ fun k => ?_
    simpa [Real.norm_eq_abs, abs_pow] using pow_le_one₀ (abs_nonneg s) hs
  rw [pgf, ← integral_map hX.aemeasurable hpow.aestronglyMeasurable, integral_countable hint]
  refine tsum_congr fun k => ?_
  rw [map_measureReal_apply hX (measurableSet_singleton k), smul_eq_mul, mul_comm]
  rfl

/-- The generating function of a sum of independent variables is the product of their
generating functions on the convergence domain `|s| ≤ 1`. -/
theorem pgf_add_of_indepFun {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : Ω → ℕ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ) {s : ℝ} (hs : |s| ≤ 1) :
    pgf (fun ω => X ω + Y ω) μ s = pgf X μ s * pgf Y μ s := by
  have hpow : Measurable (fun k : ℕ => s ^ k) := measurable_from_nat
  have hmul := (hXY.comp hpow hpow).integral_mul_eq_mul_integral
    (integrable_pow_of_abs_le_one hX hs).aestronglyMeasurable
    (integrable_pow_of_abs_le_one hY hs).aestronglyMeasurable
  simp only [pgf, pow_add]
  exact hmul

end MathlibExt.Probability
