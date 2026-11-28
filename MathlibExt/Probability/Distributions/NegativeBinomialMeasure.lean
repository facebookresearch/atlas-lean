/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.NegativeBinomial
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The negative binomial law as a measure on `ℕ`

`negBinomialMeasure θ μ` is the measure on `ℕ` that puts mass `NB(k; θ, μ)`
(`negBinomialReal θ μ k`) on each count `k`, for size `θ` and mean `μ`. For `θ > 0` and `μ ≥ 0` it
is a probability measure with mean `μ`, so laws of independent negative binomial counts can be
formed as products (`MeasureTheory.Measure.pi`).

## Main definitions

* `ProbabilityTheory.negBinomialMeasure θ μ`: the negative binomial law with size `θ` and
  mean `μ`.

## Main results

* `negBinomialReal_pos`: for `θ > 0` and `μ > 0` every count has positive mass.
* `negBinomialMeasure_singleton`, `negBinomialMeasure_real_singleton`: the mass of `{k}` is
  `NB(k; θ, μ)`.
* `isProbabilityMeasure_negBinomialMeasure`: for `θ > 0` and `μ ≥ 0` the total mass is `1`.
* `integral_negBinomialMeasure`: for `θ > 0` and `μ ≥ 0` the mean is `μ`.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory

namespace ProbabilityTheory

/-- For size `θ > 0` and mean `μ > 0` every count `k` has positive negative binomial mass
`NB(k; θ, μ) > 0`, the count `0` included. -/
theorem negBinomialReal_pos {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 < μ) (k : ℕ) :
    0 < negBinomialReal θ μ k := by
  have h := ascPochhammer_pos k θ hθ
  unfold negBinomialReal
  positivity

/-- The negative binomial law with size `θ` and mean `μ` as a measure on `ℕ`: the count `k` has
mass `NB(k; θ, μ) = θ⁽ᵏ⁾ / k! · (θ / (θ + μ)) ^ θ · (μ / (θ + μ)) ^ k` (`negBinomialReal`). The
parameter domain is `θ > 0`, `μ ≥ 0`, where it is a probability measure with mean `μ`
(`isProbabilityMeasure_negBinomialMeasure`, `integral_negBinomialMeasure`); outside it a negative
value of the formula is read as mass `0`. -/
noncomputable def negBinomialMeasure (θ μ : ℝ) : Measure ℕ :=
  Measure.sum fun k => ENNReal.ofReal (negBinomialReal θ μ k) • Measure.dirac k

/-- The mass of a count `k` is `NB(k; θ, μ)`, read as `0` where the formula is negative. -/
@[simp]
theorem negBinomialMeasure_singleton (θ μ : ℝ) (k : ℕ) :
    negBinomialMeasure θ μ {k} = ENNReal.ofReal (negBinomialReal θ μ k) := by
  rw [negBinomialMeasure, Measure.sum_apply _ (measurableSet_singleton k)]
  simp only [smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton k),
    Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq k _

/-- On the parameter domain the mass of a count `k` is `NB(k; θ, μ)`. -/
theorem negBinomialMeasure_real_singleton {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 ≤ μ) (k : ℕ) :
    (negBinomialMeasure θ μ).real {k} = negBinomialReal θ μ k := by
  rw [measureReal_def, negBinomialMeasure_singleton,
    ENNReal.toReal_ofReal (negBinomialReal_nonneg hθ hμ k)]

/-- **Normalization.** For `θ > 0` and `μ ≥ 0` the negative binomial law is a probability
measure. -/
theorem isProbabilityMeasure_negBinomialMeasure {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 ≤ μ) :
    IsProbabilityMeasure (negBinomialMeasure θ μ) := by
  constructor
  have hs := hasSum_negBinomialReal hθ hμ
  rw [negBinomialMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (negBinomialReal_nonneg hθ hμ) hs.summable, hs.tsum_eq,
    ENNReal.ofReal_one]

/-- **Mean.** For `θ > 0` and `μ ≥ 0` the negative binomial law has mean `μ`:
`∫ k, k ∂NB(θ, μ) = μ`. -/
theorem integral_negBinomialMeasure {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 ≤ μ) :
    ∫ k, (k : ℝ) ∂negBinomialMeasure θ μ = μ := by
  have hm := hasSum_mul_negBinomialReal hθ hμ
  have hc : ∀ k : ℕ, ENNReal.ofReal (negBinomialReal θ μ k) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have htoReal : ∀ k : ℕ, (ENNReal.ofReal (negBinomialReal θ μ k)).toReal = negBinomialReal θ μ k :=
    fun k => ENNReal.toReal_ofReal (negBinomialReal_nonneg hθ hμ k)
  have hsum : Summable fun k : ℕ =>
      (ENNReal.ofReal (negBinomialReal θ μ k)).toReal * ‖((id k : ℕ) : ℝ)‖ := by
    refine hm.summable.congr fun k => ?_
    simp only [htoReal, id_eq, Real.norm_natCast]
    ring
  have h := hasSum_integral_sum_dirac (f := fun k : ℕ => (k : ℝ)) (x := id) hc hsum
  refine h.unique ?_
  convert hm using 1
  funext k
  simp only [htoReal, id_eq, smul_eq_mul]
  ring

end ProbabilityTheory
