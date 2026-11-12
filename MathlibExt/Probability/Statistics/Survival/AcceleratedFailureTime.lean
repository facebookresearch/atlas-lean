/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Weibull
public import MathlibExt.Probability.Distributions.LogNormal

/-!
# Accelerated failure time

The accelerated-failure-time (AFT) model with baseline lifetime law `μ₀` and linear predictor
`η` (for instance `η = ⟪β, x⟫` for covariates `x`) is the law of `T = exp η * T₀` with
`T₀ ~ μ₀`, i.e. `log T = η + log T₀`: covariates stretch or shrink time by the acceleration
factor `exp η` (`aftMeasure`). This file proves the AFT transforms, identifies the AFT laws for
the Weibull and log-normal baselines, and separates the AFT reading from the
proportional-hazards (PH) reading.

## Main results

* Scaling law: `aftMeasure_aftMeasure` (`exp η₂ * (exp η₁ * T₀) = exp (η₁ + η₂) * T₀`),
  `aftMeasure_zero`.
* Transforms, for every `t`: survival `S(t | η) = S₀(exp (-η) t)` (`aftMeasure_Ioi`,
  `aftMeasure_real_Ioi`), distribution function (`aftMeasure_Iic`, `aftMeasure_real_Iic`),
  cumulative hazard `H(t | η) = H₀(exp (-η) t)` (`neg_log_aftMeasure_real_Ioi`), hazard rate
  `h(t | η) = exp (-η) h₀(exp (-η) t)` as a derivative of the cumulative hazard
  (`hasDerivAt_neg_log_aftMeasure_real_Ioi`), and quantiles `q_p(η) = exp η * q_p(0)`
  (`aftMeasure_real_Iic_exp_mul`).
* Parameter mapping: Weibull shape `k`, scale `l` goes to shape `k`, scale `exp η * l`
  (`aftMeasure_weibullMeasure`); log-normal `LN(μ, v)` goes to `LN(μ + η, v)`
  (`aftMeasure_logNormalMeasure`).
* PH versus AFT. `HasProportionalHazards μ₀ μ c` is the PH reading `S = S₀^c` on `[0, ∞)`,
  which multiplies hazards at a fixed time rather than rescaling time.
  `hasProportionalHazards_aftMeasure_iff` says an AFT law has a PH reading iff
  `S₀(exp (-η) t) = S₀(t)^c`.
  - **Weibull admits both readings**: `hasProportionalHazards_aftMeasure_weibullMeasure`, the
    AFT law with time ratio `exp η` is PH with hazard ratio `exp (-k η)`; equivalently
    (`neg_log_aftMeasure_weibullMeasure_real_Ioi`) `H(t | η) = exp (-k η) H₀(t)`. The PH
    log-hazard ratio is `-k η`: it differs from the AFT coefficient `η` in sign and by the
    factor `k`, so the two coefficients must not be reported interchangeably.
  - **Log-normal admits only the AFT reading**:
    `not_hasProportionalHazards_aftMeasure_logNormalMeasure`, for `v ≠ 0` and `η ≠ 0` there is
    no hazard ratio `c` at all. Iterating a PH identity would make the baseline cumulative
    hazard at `exp (μ - n η)` decay geometrically in `n`, which a Gaussian Chernoff bound
    rules out.

The hazard *rate* is handled through derivatives of the cumulative hazard `-log S`, so no
density or regularity assumption beyond the stated differentiability hypothesis is needed.

## References

* J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis of Failure Time Data*, 2nd ed.,
  Wiley (2002), §2.3.
* D. R. Cox and D. Oakes, *Analysis of Survival Data*, Chapman & Hall (1984), §5.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.AcceleratedFailureTime

open MeasureTheory ProbabilityTheory Set Real Filter Topology

open scoped ENNReal NNReal

noncomputable section

/-- **The accelerated-failure-time law** with baseline `μ₀` and linear predictor `η`: the law of
`T = exp η * T₀` for `T₀ ~ μ₀`, i.e. the pushforward of `μ₀` along `t ↦ exp η * t`. On the log
scale this is `log T = η + log T₀`, so `η` shifts the log failure time and `exp η` is the
acceleration factor (time ratio). -/
def aftMeasure (μ₀ : Measure ℝ) (η : ℝ) : Measure ℝ :=
  μ₀.map fun t => exp η * t

/-- The AFT time map `t ↦ exp η * t` is measurable. -/
lemma measurable_exp_mul (η : ℝ) : Measurable fun t : ℝ => exp η * t :=
  measurable_const_mul _

instance isProbabilityMeasure_aftMeasure (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (η : ℝ) :
    IsProbabilityMeasure (aftMeasure μ₀ η) :=
  inferInstanceAs (IsProbabilityMeasure (μ₀.map fun t => exp η * t))

/-- `exp η * s > t` iff `s > exp (-η) * t`. -/
lemma preimage_exp_mul_Ioi (η t : ℝ) :
    (fun s : ℝ => exp η * s) ⁻¹' Ioi t = Ioi (exp (-η) * t) := by
  ext s
  simp only [mem_preimage, mem_Ioi, exp_neg]
  exact (inv_mul_lt_iff₀ (exp_pos η)).symm

/-- `exp η * s ≤ t` iff `s ≤ exp (-η) * t`. -/
lemma preimage_exp_mul_Iic (η t : ℝ) :
    (fun s : ℝ => exp η * s) ⁻¹' Iic t = Iic (exp (-η) * t) := by
  have h := congrArg (·ᶜ) (preimage_exp_mul_Ioi η t)
  simpa only [← preimage_compl, compl_Ioi] using h

/-- **AFT scaling law**: accelerating twice multiplies the acceleration factors, i.e. adds the
linear predictors. -/
theorem aftMeasure_aftMeasure (μ₀ : Measure ℝ) (η₁ η₂ : ℝ) :
    aftMeasure (aftMeasure μ₀ η₁) η₂ = aftMeasure μ₀ (η₁ + η₂) := by
  rw [aftMeasure, aftMeasure, aftMeasure,
    Measure.map_map (measurable_exp_mul η₂) (measurable_exp_mul η₁)]
  congr 1
  ext t
  simp only [Function.comp_apply, exp_add]
  ring

/-- The linear predictor `0` is the baseline. -/
@[simp]
theorem aftMeasure_zero (μ₀ : Measure ℝ) : aftMeasure μ₀ 0 = μ₀ := by
  simp [aftMeasure]

/-- **AFT survival transform**: `S(t | η) = S₀(exp (-η) * t)` for every `t`. -/
theorem aftMeasure_Ioi (μ₀ : Measure ℝ) (η t : ℝ) :
    aftMeasure μ₀ η (Ioi t) = μ₀ (Ioi (exp (-η) * t)) := by
  rw [aftMeasure, Measure.map_apply (measurable_exp_mul η) measurableSet_Ioi,
    preimage_exp_mul_Ioi]

/-- **AFT survival transform**, real form. -/
theorem aftMeasure_real_Ioi (μ₀ : Measure ℝ) (η t : ℝ) :
    (aftMeasure μ₀ η).real (Ioi t) = μ₀.real (Ioi (exp (-η) * t)) := by
  rw [measureReal_def, aftMeasure_Ioi, measureReal_def]

/-- **AFT distribution-function transform**: `F(t | η) = F₀(exp (-η) * t)`. -/
theorem aftMeasure_real_Iic (μ₀ : Measure ℝ) (η t : ℝ) :
    (aftMeasure μ₀ η).real (Iic t) = μ₀.real (Iic (exp (-η) * t)) := by
  rw [aftMeasure, map_measureReal_apply (measurable_exp_mul η) measurableSet_Iic,
    preimage_exp_mul_Iic]

/-- **AFT cumulative-hazard transform**: `H(t | η) = H₀(exp (-η) * t)`, with the cumulative hazard
`H = -log S`. -/
theorem neg_log_aftMeasure_real_Ioi (μ₀ : Measure ℝ) (η t : ℝ) :
    -log ((aftMeasure μ₀ η).real (Ioi t)) = -log (μ₀.real (Ioi (exp (-η) * t))) := by
  rw [aftMeasure_real_Ioi]

/-- **AFT hazard transform**: if the baseline cumulative hazard `H₀ = -log S₀` has derivative
`h₀` (the baseline hazard rate) at `exp (-η) * t`, then the cumulative hazard of the AFT law has
derivative `exp (-η) * h₀` at `t`: `h(t | η) = exp (-η) h₀(exp (-η) t)`. Time is rescaled inside
the hazard and the hazard is multiplied by the inverse acceleration factor. -/
theorem hasDerivAt_neg_log_aftMeasure_real_Ioi (μ₀ : Measure ℝ) (η t h₀ : ℝ)
    (h : HasDerivAt (fun s => -log (μ₀.real (Ioi s))) h₀ (exp (-η) * t)) :
    HasDerivAt (fun s => -log ((aftMeasure μ₀ η).real (Ioi s))) (exp (-η) * h₀) t := by
  have hlin : HasDerivAt (fun s : ℝ => exp (-η) * s) (exp (-η)) t := by
    simpa using (hasDerivAt_id t).const_mul (exp (-η))
  have := h.comp t hlin
  simp only [neg_log_aftMeasure_real_Ioi]
  convert this using 1
  · rfl
  · ring

/-- **AFT quantile transform**: if `q` is a level-`p` point of the baseline distribution function,
`F₀(q) = p`, then `exp η * q` is a level-`p` point of the AFT law. Quantiles scale by the
acceleration factor. -/
theorem aftMeasure_real_Iic_exp_mul (μ₀ : Measure ℝ) (η q : ℝ) :
    (aftMeasure μ₀ η).real (Iic (exp η * q)) = μ₀.real (Iic q) := by
  rw [aftMeasure_real_Iic, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]

/-- **AFT distribution-function transform**, measure form. -/
theorem aftMeasure_Iic (μ₀ : Measure ℝ) (η t : ℝ) :
    aftMeasure μ₀ η (Iic t) = μ₀ (Iic (exp (-η) * t)) := by
  rw [aftMeasure, Measure.map_apply (measurable_exp_mul η) measurableSet_Iic,
    preimage_exp_mul_Iic]

/-! ### Parameter mapping for the Weibull and log-normal laws -/

/-- Weibull distribution function at `t ≥ 0`: `P(X ≤ t) = 1 - exp(-(t / l)^k)`. -/
private lemma weibullMeasure_Iic_of_nonneg {k l t : ℝ} (hk : 0 < k) (hl : 0 < l) (ht : 0 ≤ t) :
    weibullMeasure k l (Iic t) = 1 - ENNReal.ofReal (exp (-(t / l) ^ k)) := by
  have := isProbabilityMeasure_weibullMeasure hk hl
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, weibullMeasure_Ioi hk hl ht]

/-- **Weibull parameter mapping**: the AFT law with Weibull baseline of shape `k` and scale `l`
and linear predictor `η` is the Weibull law with the same shape and scale `exp η * l`. The
acceleration factor acts on the scale only. -/
theorem aftMeasure_weibullMeasure {k l : ℝ} (hk : 0 < k) (hl : 0 < l) (η : ℝ) :
    aftMeasure (weibullMeasure k l) η = weibullMeasure k (exp η * l) := by
  have hl' : 0 < exp η * l := mul_pos (exp_pos η) hl
  have := isProbabilityMeasure_weibullMeasure hk hl
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [aftMeasure_Iic]
  rcases le_or_gt a 0 with ha | ha
  · have ha' : exp (-η) * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le ha
    rw [measure_mono_null (Iic_subset_Iic.mpr ha') (weibullMeasure_Iic_zero k l),
      measure_mono_null (Iic_subset_Iic.mpr ha) (weibullMeasure_Iic_zero k _)]
  · rw [weibullMeasure_Iic_of_nonneg hk hl (mul_pos (exp_pos _) ha).le,
      weibullMeasure_Iic_of_nonneg hk hl' ha.le]
    congr 4
    rw [exp_neg]
    field_simp

/-- **Log-normal parameter mapping**: the AFT law with log-normal baseline `LN(μ, v)` and linear
predictor `η` is `LN(μ + η, v)`. The predictor shifts the log-mean; the log-variance is
unchanged. -/
theorem aftMeasure_logNormalMeasure (μ : ℝ) (v : ℝ≥0) (η : ℝ) :
    aftMeasure (logNormalMeasure μ v) η = logNormalMeasure (μ + η) v := by
  rw [aftMeasure, logNormalMeasure, logNormalMeasure,
    Measure.map_map (measurable_exp_mul η) measurable_exp, ← gaussianReal_map_add_const η,
    Measure.map_map measurable_exp (measurable_add_const η)]
  congr 1
  ext y
  simp [exp_add, mul_comm]

/-! ### Proportional hazards versus accelerated failure time -/

/-- **Proportional-hazards reading** with hazard ratio `c`: the survival function of `μ` is the
`c`-th power of that of `μ₀` on `[0, ∞)`, `S(t) = S₀(t)^c`. Where `S₀(t) > 0` this says the
cumulative hazards satisfy `H(t) = c H₀(t)`, and hence, where they are differentiable, the hazard
rates satisfy `h(t) = c h₀(t)`. This is a statement about multiplying hazards at the same time
`t`; the AFT reading `μ = aftMeasure μ₀ η` instead rescales time. -/
def HasProportionalHazards (μ₀ μ : Measure ℝ) (c : ℝ) : Prop :=
  ∀ t, 0 ≤ t → μ.real (Ioi t) = μ₀.real (Ioi t) ^ c

/-- **When an AFT law is also a PH law**: the AFT law with predictor `η` has the PH reading with
hazard ratio `c` iff the baseline survival function satisfies `S₀(exp (-η) t) = S₀(t)^c` on
`[0, ∞)`. -/
theorem hasProportionalHazards_aftMeasure_iff (μ₀ : Measure ℝ) (η c : ℝ) :
    HasProportionalHazards μ₀ (aftMeasure μ₀ η) c ↔
      ∀ t, 0 ≤ t → μ₀.real (Ioi (exp (-η) * t)) = μ₀.real (Ioi t) ^ c := by
  simp only [HasProportionalHazards, aftMeasure_real_Ioi]

/-- **The Weibull AFT law admits both readings.** With Weibull baseline of shape `k`, the AFT law
with predictor `η` (time ratio `exp η`) is also a PH law with hazard ratio `exp (-k η)`. -/
theorem hasProportionalHazards_aftMeasure_weibullMeasure {k l : ℝ} (hk : 0 < k) (hl : 0 < l)
    (η : ℝ) :
    HasProportionalHazards (weibullMeasure k l) (aftMeasure (weibullMeasure k l) η)
      (exp (-(k * η))) := by
  rw [hasProportionalHazards_aftMeasure_iff]
  intro t ht
  have hη : 0 ≤ exp (-η) := (exp_pos _).le
  rw [weibullMeasure_real_Ioi hk hl (mul_nonneg hη ht), weibullMeasure_real_Ioi hk hl ht,
    ← exp_mul, mul_div_assoc, mul_rpow hη (div_nonneg ht hl.le), ← exp_mul]
  congr 1
  ring_nf

/-- **Weibull cumulative hazard under AFT**: `H(t | η) = exp (-k η) H₀(t)` for `t ≥ 0`, where
`H₀(t) = (t / l)^k`. -/
theorem neg_log_aftMeasure_weibullMeasure_real_Ioi {k l t : ℝ} (hk : 0 < k) (hl : 0 < l)
    (ht : 0 ≤ t) (η : ℝ) :
    -log ((aftMeasure (weibullMeasure k l) η).real (Ioi t)) =
      exp (-(k * η)) * -log ((weibullMeasure k l).real (Ioi t)) := by
  rw [hasProportionalHazards_aftMeasure_weibullMeasure hk hl η t ht,
    log_rpow (by rw [weibullMeasure_real_Ioi hk hl ht]; exact exp_pos _)]
  ring

/-- Log-normal survival function: `P(X > t) = P(Y > log t)` for `t > 0`, `Y ~ N(μ, v)`. -/
theorem logNormalMeasure_real_Ioi (μ : ℝ) (v : ℝ≥0) {t : ℝ} (ht : 0 < t) :
    (logNormalMeasure μ v).real (Ioi t) = (gaussianReal μ v).real (Ioi (log t)) := by
  rw [logNormalMeasure, map_measureReal_apply measurable_exp measurableSet_Ioi]
  congr 1
  ext y
  exact (log_lt_iff_lt_exp ht).symm

/-- A non-degenerate Gaussian charges every set of positive Lebesgue measure. -/
private lemma gaussianReal_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {s : Set ℝ}
    (hs : volume s ≠ 0) : gaussianReal μ v s ≠ 0 :=
  fun h => hs (gaussianReal_absolutelyContinuous' μ hv h)

private lemma gaussianReal_real_Ioi_pos (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    0 < (gaussianReal μ v).real (Ioi a) :=
  ENNReal.toReal_pos (gaussianReal_ne_zero μ hv (by simp)) (measure_ne_top _ _)

private lemma gaussianReal_real_Ioi_lt_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    (gaussianReal μ v).real (Ioi a) < 1 := by
  have h := ENNReal.toReal_pos (gaussianReal_ne_zero μ hv (s := Iic a) (by simp))
    (measure_ne_top _ _)
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  rw [← measureReal_def] at h
  linarith

/-- **Gaussian lower-tail Chernoff bound**: `P(Y ≤ μ - z) ≤ exp(-z² / (2v))` for `z ≥ 0`. -/
private lemma gaussianReal_real_Iic_sub_le (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {z : ℝ} (hz : 0 ≤ z) :
    (gaussianReal μ v).real (Iic (μ - z)) ≤ exp (-(z ^ 2 / (2 * v))) := by
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm)
  have h := measure_le_le_exp_mul_mgf (X := id) (μ := gaussianReal μ v) (μ - z)
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hv'.le)
    (integrable_exp_mul_gaussianReal (-z / v))
  rw [mgf_id_gaussianReal, ← exp_add] at h
  refine h.trans_eq (congrArg exp ?_)
  field_simp
  ring

/-- The Gaussian survival function `q(x) = P(Y > x)` is not self-similar under a shift: no
`η > 0`, `c > 0` give `q(x - η) = q(x)^c` for all `x`. Iterating would force the cumulative
hazard `-log q(μ - n η) = cⁿ (-log q(μ))` to decay only geometrically in `n`, while the
Chernoff bound makes it decay like `exp(-(n η)² / (2v))`. -/
private lemma gaussianReal_real_Ioi_not_selfSimilar (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {η c : ℝ}
    (hη : 0 < η) (hc : 0 < c)
    (h : ∀ x, (gaussianReal μ v).real (Ioi (x - η)) = (gaussianReal μ v).real (Ioi x) ^ c) :
    False := by
  set G := gaussianReal μ v
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm)
  set s := G.real (Ioi μ) with hs_def
  have hs0 : 0 < s := gaussianReal_real_Ioi_pos μ hv μ
  have hs1 : s < 1 := gaussianReal_real_Ioi_lt_one μ hv μ
  have hiter : ∀ n : ℕ, G.real (Ioi (μ - n * η)) = s ^ (c ^ n) := by
    intro n
    induction n with
    | zero => simp [hs_def]
    | succ n ih =>
      have e : μ - ((n + 1 : ℕ) : ℝ) * η = (μ - n * η) - η := by push_cast; ring
      rw [e, h, ih, ← rpow_mul hs0.le, pow_succ]
  set K := -log s with hK_def
  have hK : 0 < K := neg_pos.mpr (log_neg hs0 hs1)
  -- the geometric-versus-Gaussian comparison at every `n`
  have hbound : ∀ n : ℕ, c ^ n * K * s ≤ exp (-((n * η) ^ 2 / (2 * v))) := by
    intro n
    have hnη : 0 ≤ (n : ℝ) * η := mul_nonneg n.cast_nonneg hη.le
    set qn := G.real (Ioi (μ - n * η))
    have hqn0 : 0 < qn := gaussianReal_real_Ioi_pos μ hv _
    have hqns : s ≤ qn := measureReal_mono (Ioi_subset_Ioi (by linarith))
    have hlog : -log qn = c ^ n * K := by
      simp only [qn, hiter n, log_rpow hs0, hK_def]; ring
    have htail : 1 - qn ≤ exp (-((n * η) ^ 2 / (2 * v))) := by
      have := gaussianReal_real_Iic_sub_le μ hv hnη
      rwa [← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi] at this
    have h1 : -log qn ≤ (1 - qn) / qn := by
      have := one_sub_inv_le_log_of_pos hqn0
      rw [sub_div, div_self hqn0.ne', one_div]
      linarith
    have h2 : (1 - qn) / qn ≤ (1 - qn) / s :=
      div_le_div_of_nonneg_left (by linarith [measureReal_le_one (μ := G) (s := Ioi (μ - n * η))])
        hs0 hqns
    have h3 : c ^ n * K ≤ exp (-((n * η) ^ 2 / (2 * v))) / s :=
      hlog ▸ h1.trans (h2.trans (div_le_div_of_nonneg_right htail hs0.le))
    rwa [le_div_iff₀ hs0] at h3
  -- pick `n` large enough that the quadratic exponent beats the linear one
  set a := η ^ 2 / (2 * v) with ha_def
  have ha : 0 < a := by positivity
  set A := |log c| + |log (K * s)| + 1
  set n : ℕ := ⌈A / a⌉₊ + 1
  have hn1 : (1 : ℝ) ≤ n := by simp [n]
  have hna : A ≤ n * a := by
    have : A / a ≤ n := (Nat.le_ceil _).trans (by simp [n])
    rwa [div_le_iff₀ ha] at this
  have hlogb := log_le_log (by positivity) (hbound n)
  rw [log_exp, log_mul (by positivity) hs0.ne', log_mul (by positivity) hK.ne',
    log_pow] at hlogb
  have hsq : (n * η) ^ 2 / (2 * v) = n * (n * a) := by rw [ha_def]; ring
  rw [hsq] at hlogb
  have e1 : -(n * |log c|) ≤ n * log c := by
    have := neg_abs_le (log c); nlinarith
  have e2 : -|log (K * s)| ≤ log K + log s := by
    rw [← log_mul hK.ne' hs0.ne']; exact neg_abs_le _
  have e3 : n * A ≤ n * (n * a) := mul_le_mul_of_nonneg_left hna (by linarith)
  have e4 : n * |log c| + |log (K * s)| + 1 ≤ n * A := by
    simp only [A]; nlinarith [abs_nonneg (log (K * s))]
  linarith

/-- **The log-normal AFT law admits no proportional-hazards reading.** For a non-degenerate
log-normal baseline (`v ≠ 0`) and any non-zero linear predictor `η`, the AFT law
`aftMeasure (logNormalMeasure μ v) η = logNormalMeasure (μ + η) v` is a PH law with respect to
the baseline for no hazard ratio `c` whatsoever. Contrast
`hasProportionalHazards_aftMeasure_weibullMeasure`. -/
theorem not_hasProportionalHazards_aftMeasure_logNormalMeasure (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {η : ℝ} (hη : η ≠ 0) (c : ℝ) :
    ¬ HasProportionalHazards (logNormalMeasure μ v) (aftMeasure (logNormalMeasure μ v) η) c := by
  intro hPH
  rw [hasProportionalHazards_aftMeasure_iff] at hPH
  set q : ℝ → ℝ := fun x => (gaussianReal μ v).real (Ioi x) with hq_def
  have hq : ∀ x, q (x - η) = q x ^ c := by
    intro x
    have := hPH (exp x) (exp_pos x).le
    rwa [← exp_add, logNormalMeasure_real_Ioi _ _ (exp_pos _),
      logNormalMeasure_real_Ioi _ _ (exp_pos _), log_exp, log_exp, neg_add_eq_sub] at this
  have hc : 0 < c := by
    by_contra hc
    push Not at hc
    have h1 : 1 ≤ q μ ^ c := one_le_rpow_of_pos_of_le_one_of_nonpos
      (gaussianReal_real_Ioi_pos μ hv μ) (gaussianReal_real_Ioi_lt_one μ hv μ).le hc
    have h2 := gaussianReal_real_Ioi_lt_one μ hv (μ - η)
    change q (μ - η) < 1 at h2
    linarith [hq μ]
  rcases lt_or_gt_of_ne hη with hneg | hpos
  · refine gaussianReal_real_Ioi_not_selfSimilar μ hv (neg_pos.mpr hneg) (inv_pos.mpr hc)
      fun x => ?_
    have h := hq (x - -η)
    rw [show x - -η - η = x by ring] at h
    change q (x - -η) = q x ^ c⁻¹
    rw [h, ← rpow_mul (gaussianReal_real_Ioi_pos μ hv _).le, mul_inv_cancel₀ hc.ne', rpow_one]
  · exact gaussianReal_real_Ioi_not_selfSimilar μ hv hpos hc hq

end

end MathlibExt.Probability.Statistics.AcceleratedFailureTime
