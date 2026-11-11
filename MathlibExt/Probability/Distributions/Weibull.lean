/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Weibull law

`weibullMeasure k l` is the Weibull law with shape `k` and scale `l`, defined by its Lebesgue
density on `x > 0`
`f(x) = (k / l) (x / l)^{k-1} exp(-(x / l)^k)`.
Outside `k > 0, l > 0` the definition is totalized to the zero measure.

The survival function `P(X > t) = exp(-(t / l)^k)` for `t ≥ 0` comes from the fundamental
theorem of calculus on `(t, ∞)`: on `x > 0` the density is the derivative of
`-exp(-(x / l)^k)`, which is continuous at `0` and tends to `0` at infinity. Total mass `1` is
the case `t = 0`, since the density vanishes on `(-∞, 0]`.

## Main results

* `ProbabilityTheory.weibullMeasure_Ioi`: `P(X > t) = exp(-(t / l)^k)` for `t ≥ 0`.
* `ProbabilityTheory.isProbabilityMeasure_weibullMeasure`.
* `ProbabilityTheory.neg_log_weibullMeasure_real_Ioi`: the cumulative hazard is `(t / l)^k`.
* `ProbabilityTheory.weibullMeasure_one`: shape `1` is the exponential law of rate `l⁻¹`.

## References

* W. Weibull, *A statistical distribution function of wide applicability*, J. Appl. Mech. 18
  (1951), 293–297.
-/

open MeasureTheory Set Real Filter Topology

open scoped ENNReal

namespace ProbabilityTheory

@[expose] public section

noncomputable section

/-- The density of the Weibull law with shape `k` and scale `l`:
`(k / l) (x / l)^{k-1} exp(-(x / l)^k)` for `x > 0` and `0` for `x ≤ 0`. -/
def weibullPDFReal (k l x : ℝ) : ℝ :=
  if 0 < x then k / l * (x / l) ^ (k - 1) * exp (-(x / l) ^ k) else 0

/-- **The Weibull law** with shape `k` and scale `l`: the measure with Lebesgue density
`weibullPDFReal k l`. It is a probability measure for `k, l > 0`
(`isProbabilityMeasure_weibullMeasure`). Outside that range the definition is totalized to the
zero measure, as `snedecorFMeasure` is with zero degrees of freedom. -/
def weibullMeasure (k l : ℝ) : Measure ℝ :=
  if 0 < k ∧ 0 < l then volume.withDensity fun x => ENNReal.ofReal (weibullPDFReal k l x)
  else 0

lemma weibullMeasure_of_pos {k l : ℝ} (hk : 0 < k) (hl : 0 < l) :
    weibullMeasure k l = volume.withDensity fun x => ENNReal.ofReal (weibullPDFReal k l x) :=
  ite_eq_left ⟨hk, hl⟩

lemma weibullMeasure_of_nonpos_left {k : ℝ} (hk : k ≤ 0) (l : ℝ) : weibullMeasure k l = 0 :=
  ite_eq_right fun h => hk.not_gt h.1

lemma weibullMeasure_of_nonpos_right (k : ℝ) {l : ℝ} (hl : l ≤ 0) : weibullMeasure k l = 0 :=
  ite_eq_right fun h => hl.not_gt h.2

@[fun_prop]
lemma measurable_weibullPDFReal (k l : ℝ) : Measurable (weibullPDFReal k l) :=
  Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

/-- On `x > 0` the Weibull density is the derivative of `-exp(-(x / l)^k)`. -/
private lemma hasDerivAt_weibull_antideriv {k l x : ℝ} (hl : 0 < l) (hx : 0 < x) :
    HasDerivAt (fun y => -exp (-(y / l) ^ k)) (weibullPDFReal k l x) x := by
  have hxl : 0 < x / l := div_pos hx hl
  have h1 : HasDerivAt (fun y => y / l) (1 / l) x := (hasDerivAt_id x).div_const l
  have h2 : HasDerivAt (fun y => -exp (-(y / l) ^ k))
      (-(exp (-(x / l) ^ k) * -(1 / l * k * (x / l) ^ (k - 1)))) x :=
    (h1.rpow_const (p := k) (Or.inl hxl.ne')).neg.exp.neg
  rw [weibullPDFReal, ite_eq_left hx]
  exact h2.congr_deriv (by ring)

private lemma tendsto_weibull_antideriv {k l : ℝ} (hk : 0 < k) (hl : 0 < l) :
    Tendsto (fun y => -exp (-(y / l) ^ k)) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => (y / l) ^ k) atTop atTop :=
    (tendsto_rpow_atTop hk).comp (tendsto_id.atTop_div_const hl)
  simpa using (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h)).neg

private lemma continuousWithinAt_weibull_antideriv {k l t : ℝ} (hk : 0 < k) :
    ContinuousWithinAt (fun y => -exp (-(y / l) ^ k)) (Ici t) t :=
  ((((continuous_id.div_const l).continuousAt.rpow_const (Or.inr hk.le)).neg).rexp.neg
    ).continuousWithinAt

/-- **Weibull survival function**, as a Bochner integral of the density. -/
private lemma integral_weibullPDFReal_Ioi {k l t : ℝ} (hk : 0 < k) (hl : 0 < l) (ht : 0 ≤ t) :
    ∫ x in Ioi t, weibullPDFReal k l x = exp (-(t / l) ^ k) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (continuousWithinAt_weibull_antideriv hk)
    (fun x hx => hasDerivAt_weibull_antideriv hl (ht.trans_lt hx))
    (fun x hx => ?_) (tendsto_weibull_antideriv hk hl)]
  · ring
  · rw [weibullPDFReal, ite_eq_left (ht.trans_lt hx)]
    have : 0 < x / l := div_pos (ht.trans_lt hx) hl
    positivity

private lemma integrableOn_weibullPDFReal_Ioi {k l t : ℝ} (hk : 0 < k) (hl : 0 < l)
    (ht : 0 ≤ t) : IntegrableOn (weibullPDFReal k l) (Ioi t) := by
  refine integrableOn_Ioi_deriv_of_nonneg (continuousWithinAt_weibull_antideriv hk)
    (fun x hx => hasDerivAt_weibull_antideriv hl (ht.trans_lt hx))
    (fun x hx => ?_) (tendsto_weibull_antideriv hk hl)
  rw [weibullPDFReal, ite_eq_left (ht.trans_lt hx)]
  have : 0 < x / l := div_pos (ht.trans_lt hx) hl
  positivity

/-- **Weibull survival function**: `P(X > t) = exp(-(t / l)^k)` for `t ≥ 0`. -/
theorem weibullMeasure_Ioi {k l t : ℝ} (hk : 0 < k) (hl : 0 < l) (ht : 0 ≤ t) :
    weibullMeasure k l (Ioi t) = ENNReal.ofReal (exp (-(t / l) ^ k)) := by
  rw [weibullMeasure_of_pos hk hl, withDensity_apply _ measurableSet_Ioi,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_weibullPDFReal_Ioi hk hl ht),
    integral_weibullPDFReal_Ioi hk hl ht]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [weibullPDFReal, ite_eq_left (ht.trans_lt hx)]
  have : 0 < x / l := div_pos (ht.trans_lt hx) hl
  positivity

/-- The Weibull law puts no mass on `(-∞, 0]`. -/
theorem weibullMeasure_Iic_zero (k l : ℝ) : weibullMeasure k l (Iic 0) = 0 := by
  by_cases h : 0 < k ∧ 0 < l
  · rw [weibullMeasure_of_pos h.1 h.2, withDensity_apply _ measurableSet_Iic,
      setLIntegral_congr_fun measurableSet_Iic (g := fun _ => 0)
        (fun x (hx : x ≤ 0) => by simp [weibullPDFReal, not_lt.mpr hx])]
    simp
  · simp [weibullMeasure, h]

theorem isProbabilityMeasure_weibullMeasure {k l : ℝ} (hk : 0 < k) (hl : 0 < l) :
    IsProbabilityMeasure (weibullMeasure k l) where
  measure_univ := by
    rw [← Iic_union_Ioi (a := (0 : ℝ)), measure_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi,
      weibullMeasure_Iic_zero, weibullMeasure_Ioi hk hl le_rfl]
    simp [zero_div, zero_rpow hk.ne']

/-- **Weibull survival function**, real form: `P(X > t) = exp(-(t / l)^k)` for `t ≥ 0`. -/
theorem weibullMeasure_real_Ioi {k l t : ℝ} (hk : 0 < k) (hl : 0 < l) (ht : 0 ≤ t) :
    (weibullMeasure k l).real (Ioi t) = exp (-(t / l) ^ k) := by
  rw [measureReal_def, weibullMeasure_Ioi hk hl ht, ENNReal.toReal_ofReal (exp_pos _).le]

/-- **Weibull cumulative hazard**: `-log P(X > t) = (t / l)^k` for `t ≥ 0`. -/
theorem neg_log_weibullMeasure_real_Ioi {k l t : ℝ} (hk : 0 < k) (hl : 0 < l) (ht : 0 ≤ t) :
    -log ((weibullMeasure k l).real (Ioi t)) = (t / l) ^ k := by
  rw [weibullMeasure_real_Ioi hk hl ht, log_exp, neg_neg]

/-- **Shape `1` is exponential**: the Weibull law with shape `1` and scale `l` is the
exponential law of rate `l⁻¹`. The two densities differ only at `x = 0`. -/
theorem weibullMeasure_one {l : ℝ} (hl : 0 < l) : weibullMeasure 1 l = expMeasure l⁻¹ := by
  rw [weibullMeasure_of_pos one_pos hl, expMeasure, gammaMeasure]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.ae_ne volume 0] with x hx
  rw [gammaPDF_eq]
  congr 1
  rcases lt_or_gt_of_ne hx with hx' | hx'
  · simp [weibullPDFReal, not_lt.mpr hx'.le, not_le.mpr hx']
  · simp only [weibullPDFReal, ite_eq_left hx', ite_eq_left hx'.le, sub_self, rpow_zero, rpow_one,
      Gamma_one, div_one, mul_one]
    rw [div_eq_inv_mul, inv_mul_eq_div, one_div]
    ring_nf

end

end

end ProbabilityTheory
