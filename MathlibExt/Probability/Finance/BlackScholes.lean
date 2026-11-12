/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.LogNormal
public import Mathlib.Probability.CDF

/-!
# The Black-Scholes call formula as a lognormal expectation

Under the assumed risk-neutral law of the terminal price,
`S_T = S0 exp((r - σ²/2) T + σ √T Z)` with `Z` standard normal (the log-normal law
`riskNeutralLaw S0 r σ T`, whose mean is `S0 e^{rT}`), the discounted expected payoff of a
European call with strike `K` is the Black-Scholes price `S0 Φ(d₁) - K e^{-rT} Φ(d₂)`, where
`d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)`, `d₂ = d₁ - σ √T` and `Φ` is the standard normal
cdf. This is an identity for an expectation under an assumed law, not a continuous-time pricing
theorem: no stochastic calculus, replication or continuous-time no-arbitrage argument is
formalized. There are no dividends; `S0`, `K`, `σ` and `T` are positive, and any interest rate
`r` is allowed.

## Main results

* `integral_id_riskNeutralLaw`: the assumed law has mean `S0 e^{rT}`.
* `setIntegral_Ioi_exp_mul_gaussianReal`: `E[e^{sZ}; Z > a] = e^{s²/2} Φ(s - a)`.
* `discounted_integral_call_riskNeutralLaw`: the Black-Scholes formula.

## References

* F. Black and M. Scholes, *The pricing of options and corporate liabilities*, J. Polit.
  Econ. 81 (1973), 637–654.
* J. C. Hull, *Options, Futures, and Other Derivatives*, Chapter 15 (risk-neutral valuation
  of the Black-Scholes-Merton formula).
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.BlackScholes

open scoped NNReal

open MeasureTheory ProbabilityTheory Real

/-- The assumed risk-neutral law of the terminal price `S_T = S0 exp((r - σ²/2) T + σ √T Z)`
with `Z` standard normal: the log-normal law with log-mean `log S0 + (r - σ²/2) T` and
log-variance `σ² T`. No dividends. -/
noncomputable def riskNeutralLaw (S0 r σ T : ℝ) : Measure ℝ :=
  logNormalMeasure (log S0 + (r - σ ^ 2 / 2) * T) (Real.toNNReal (σ ^ 2 * T))

/-- The Black-Scholes `d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)`. -/
noncomputable def d1 (S0 K r σ T : ℝ) : ℝ :=
  (log (S0 / K) + (r + σ ^ 2 / 2) * T) / (σ * √T)

/-- The Black-Scholes `d₂ = d₁ - σ √T`. -/
noncomputable def d2 (S0 K r σ T : ℝ) : ℝ :=
  d1 S0 K r σ T - σ * √T

/-- The Black-Scholes price of a European call with strike `K` and maturity `T`:
`S0 Φ(d₁) - K e^{-rT} Φ(d₂)`, with `Φ = cdf (gaussianReal 0 1)` the standard normal cdf. -/
noncomputable def blackScholesCall (S0 K r σ T : ℝ) : ℝ :=
  S0 * cdf (gaussianReal 0 1) (d1 S0 K r σ T) -
    K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S0 K r σ T)

/-- The assumed law has mean `S0 e^{rT}`: the discounted terminal mean is `S0`. -/
theorem integral_id_riskNeutralLaw {S0 r σ T : ℝ} (hS0 : 0 < S0) (hT : 0 ≤ T) :
    ∫ x, x ∂(riskNeutralLaw S0 r σ T) = S0 * exp (r * T) := by
  unfold riskNeutralLaw
  rw [integral_id_logNormalMeasure]
  have hnonneg : 0 ≤ σ ^ 2 * T := mul_nonneg (sq_nonneg σ) hT
  rw [Real.coe_toNNReal _ hnonneg]
  have hexp : exp (log S0 + (r - σ ^ 2 / 2) * T + σ ^ 2 * T / 2) = S0 * exp (r * T) := by
    have h1 : log S0 + (r - σ ^ 2 / 2) * T + σ ^ 2 * T / 2 = log S0 + r * T := by ring
    rw [h1, exp_add, exp_log hS0]
  exact hexp

/-- **Truncated Gaussian exponential identity**: for a standard normal `Z`,
`E[e^{sZ}; Z > a] = e^{s²/2} Φ(s - a)`. -/
theorem setIntegral_Ioi_exp_mul_gaussianReal (s a : ℝ) :
    ∫ z in Set.Ioi a, exp (s * z) ∂(gaussianReal 0 1) =
      exp (s ^ 2 / 2) * cdf (gaussianReal 0 1) (s - a) := by
  have hv1 : (1 : ℝ≥0) ≠ 0 := by simp
  have hsq : ∀ z : ℝ, exp (s * z) * gaussianPDFReal 0 1 z
      = exp (s ^ 2 / 2) * gaussianPDFReal s 1 z := by
    intro z
    unfold gaussianPDFReal
    simp only [NNReal.coe_one]
    have h : s * z + (-(z - 0) ^ 2 / (2 * (1 : ℝ)))
        = s ^ 2 / 2 + (-(z - s) ^ 2 / (2 * (1 : ℝ))) := by ring
    calc exp (s * z) * ((√(2 * π * 1))⁻¹ * exp (-(z - 0) ^ 2 / (2 * 1)))
        = (√(2 * π * 1))⁻¹ * (exp (s * z) * exp (-(z - 0) ^ 2 / (2 * 1))) := by ring
      _ = (√(2 * π * 1))⁻¹ * exp (s * z + (-(z - 0) ^ 2 / (2 * 1))) := by rw [exp_add]
      _ = (√(2 * π * 1))⁻¹ * exp (s ^ 2 / 2 + (-(z - s) ^ 2 / (2 * 1))) := by rw [h]
      _ = (√(2 * π * 1))⁻¹ * (exp (s ^ 2 / 2) * exp (-(z - s) ^ 2 / (2 * 1))) := by rw [exp_add]
      _ = exp (s ^ 2 / 2) * ((√(2 * π * 1))⁻¹ * exp (-(z - s) ^ 2 / (2 * 1))) := by ring
  have hmeas : Measurable (gaussianPDF (0 : ℝ) (1 : ℝ≥0)) := measurable_gaussianPDF 0 1
  have hs : MeasurableSet (Set.Ioi a) := measurableSet_Ioi
  have hLHS : ∫ z in Set.Ioi a, exp (s * z) ∂(gaussianReal 0 1)
      = exp (s ^ 2 / 2) * ∫ z in Set.Ioi a, gaussianPDFReal s 1 z := by
    rw [gaussianReal_of_var_ne_zero 0 hv1]
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hmeas
      (ae_of_all _ fun x => gaussianPDF_lt_top) _ hs]
    have h1 : (∫ z in Set.Ioi a, (gaussianPDF 0 1 z).toReal • exp (s * z)) =
        ∫ z in Set.Ioi a, exp (s ^ 2 / 2) * gaussianPDFReal s 1 z := by
      apply setIntegral_congr_ae hs
      filter_upwards with z hz
      simp only [toReal_gaussianPDF, smul_eq_mul]
      rw [mul_comm]
      exact hsq z
    rw [h1, ← integral_const_mul]
  have hA : ∫ z in Set.Ioi a, gaussianPDFReal s 1 z
      = (gaussianReal s 1).real (Set.Ioi a) := by
    have h := gaussianReal_apply_eq_integral s hv1 (Set.Ioi a)
    rw [measureReal_def, h, ENNReal.toReal_ofReal]
    apply integral_nonneg_of_ae
    filter_upwards with x
    exact gaussianPDFReal_nonneg s 1 x
  have hB : (gaussianReal s 1).real (Set.Ioi a)
      = (gaussianReal 0 1).real (Set.Ioi (a - s)) := by
    have hmap : (gaussianReal (0 : ℝ) (1 : ℝ≥0)).map (· + s) = gaussianReal s 1 := by
      have h := gaussianReal_map_add_const (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) s
      simpa using h
    conv_lhs => rw [← hmap]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Ioi]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro h; linarith
    · intro h; linarith
  have hnull : NullSingletonClass (gaussianReal (0 : ℝ) (1 : ℝ≥0)) :=
    nullSingletonClass_gaussianReal hv1
  have hC : (gaussianReal (0 : ℝ) (1 : ℝ≥0)).real (Set.Ioi (a - s))
      = cdf (gaussianReal 0 1) (s - a) := by
    have hneg : (gaussianReal (0 : ℝ) (1 : ℝ≥0)).map (fun x => -x) = gaussianReal 0 1 := by
      have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      simpa using h
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi (a - s) = Set.Iio (s - a) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
      constructor
      · intro h; linarith
      · intro h; linarith
    calc (gaussianReal (0 : ℝ) (1 : ℝ≥0)).real (Set.Ioi (a - s))
        = ((gaussianReal (0 : ℝ) (1 : ℝ≥0)).map (fun x => -x)).real (Set.Ioi (a - s)) := by
          rw [hneg]
      _ = (gaussianReal (0 : ℝ) (1 : ℝ≥0)).real ((fun x : ℝ => -x) ⁻¹' Set.Ioi (a - s)) := by
          rw [map_measureReal_apply (by fun_prop) measurableSet_Ioi]
      _ = (gaussianReal (0 : ℝ) (1 : ℝ≥0)).real (Set.Iio (s - a)) := by rw [hpre]
      _ = (gaussianReal (0 : ℝ) (1 : ℝ≥0)).real (Set.Iic (s - a)) :=
          measureReal_congr Iio_ae_eq_Iic
      _ = cdf (gaussianReal 0 1) (s - a) := (cdf_eq_real _ _).symm
  rw [hLHS, hA, hB, hC]

/-- **Black-Scholes formula** (expectation under the assumed law, not a continuous-time
pricing theorem): for `S0, K, σ, T > 0` and any interest rate `r`, the discounted expected call
payoff under the log-normal risk-neutral law is the Black-Scholes price. -/
theorem discounted_integral_call_riskNeutralLaw {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) :
    exp (-(r * T)) * ∫ x, max (x - K) 0 ∂(riskNeutralLaw S0 r σ T) =
      blackScholesCall S0 K r σ T := by
  have hTnn : 0 ≤ T := le_of_lt hT
  have hsqrt_pos : 0 < √T := Real.sqrt_pos.mpr hT
  have hc_pos : 0 < σ * √T := mul_pos hσ hsqrt_pos
  have hsq : (σ * √T) ^ 2 = σ ^ 2 * T := by rw [mul_pow, Real.sq_sqrt hTnn]
  have hnonneg : 0 ≤ σ ^ 2 * T := mul_nonneg (sq_nonneg σ) hTnn
  have hcoe : (Real.toNNReal (σ ^ 2 * T) : ℝ) = σ ^ 2 * T :=
    Real.coe_toNNReal _ hnonneg
  have hS0ne : S0 ≠ 0 := ne_of_gt hS0
  have hKne : K ≠ 0 := ne_of_gt hK
  have hlogdiv : log (S0 / K) = log S0 - log K := Real.log_div hS0ne hKne
  have hsq_sqrt : √T ^ 2 = T := Real.sq_sqrt hTnn
  have hv1 : (1 : ℝ≥0) ≠ 0 := by simp
  have hnull : NullSingletonClass (gaussianReal (0 : ℝ) (1 : ℝ≥0)) :=
    nullSingletonClass_gaussianReal hv1
  have hthresh : ∀ z : ℝ,
      exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) > K
        ↔ -d2 S0 K r σ T < z := by
    intro z
    simp only [d2, d1]
    have hexp_gt : exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) > K
        ↔ (log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z > log K := by
      constructor
      · intro h
        have h1 : log (exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z)) > log K :=
          Real.log_lt_log hK h
        rwa [Real.log_exp] at h1
      · intro h
        have h2 : exp (log K)
            < exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) :=
          Real.exp_lt_exp.mpr h
        rwa [Real.exp_log hK] at h2
    rw [hexp_gt]
    have hcz : (log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z > log K
        ↔ z > (log K - (log S0 + (r - σ ^ 2 / 2) * T)) / (σ * √T) := by
      rw [gt_iff_lt, gt_iff_lt, div_lt_iff₀ hc_pos]
      constructor
      · intro h; linarith
      · intro h; linarith
    rw [hcz]
    have hEq : (log K - (log S0 + (r - σ ^ 2 / 2) * T)) / (σ * √T)
        = -((log (S0 / K) + (r + σ ^ 2 / 2) * T) / (σ * √T) - σ * √T) := by
      rw [hlogdiv]
      have hc_ne : (σ * √T) ≠ 0 := ne_of_gt hc_pos
      field_simp
      have h1 : (σ * √T) ^ 2 = σ ^ 2 * T := by rw [mul_pow, hsq_sqrt]
      nlinarith [h1]
    rw [gt_iff_lt, hEq]
  have hmap : (gaussianReal (0 : ℝ) (1 : ℝ≥0)).map
        (fun z => (log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z)
        = gaussianReal (log S0 + (r - σ ^ 2 / 2) * T)
          (Real.toNNReal (σ ^ 2 * T)) := by
    have h1 : (gaussianReal (0 : ℝ) (1 : ℝ≥0)).map ((σ * √T) * ·)
        = gaussianReal 0 (Real.toNNReal (σ ^ 2 * T)) := by
      have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (σ * √T)
      simp only [mul_zero] at h
      have hvar : (NNReal.mk ((σ * √T) ^ 2) (sq_nonneg _) * 1 : ℝ≥0)
          = Real.toNNReal (σ ^ 2 * T) := by
        apply NNReal.eq
        simp only [mul_one, NNReal.coe_mk]
        rw [hcoe]
        exact hsq
      rw [hvar] at h
      exact h
    have h2 : (gaussianReal (0 : ℝ) (Real.toNNReal (σ ^ 2 * T))).map
          ((log S0 + (r - σ ^ 2 / 2) * T) + ·)
        = gaussianReal (log S0 + (r - σ ^ 2 / 2) * T)
          (Real.toNNReal (σ ^ 2 * T)) := by
      have h := gaussianReal_map_const_add (μ := (0 : ℝ))
        (v := Real.toNNReal (σ ^ 2 * T)) (log S0 + (r - σ ^ 2 / 2) * T)
      simpa using h
    have hcomp : (fun z : ℝ => (log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z)
        = (fun y => (log S0 + (r - σ ^ 2 / 2) * T) + y)
          ∘ (fun z => (σ * √T) * z) := by
      ext z; simp [Function.comp]
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1, h2]
  have hrisk : riskNeutralLaw S0 r σ T
      = (gaussianReal (log S0 + (r - σ ^ 2 / 2) * T)
        (Real.toNNReal (σ ^ 2 * T))).map exp := rfl
  have hI1 : ∫ x, max (x - K) 0 ∂(riskNeutralLaw S0 r σ T)
      = ∫ y, max (exp y - K) 0
        ∂(gaussianReal (log S0 + (r - σ ^ 2 / 2) * T)
          (Real.toNNReal (σ ^ 2 * T))) := by
    rw [hrisk]
    rw [integral_map measurable_exp.aemeasurable (by fun_prop)]
  have hI2 : ∫ y, max (exp y - K) 0
        ∂(gaussianReal (log S0 + (r - σ ^ 2 / 2) * T)
          (Real.toNNReal (σ ^ 2 * T)))
      = ∫ z, max (exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K) 0
        ∂(gaussianReal 0 1) := by
    rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ z : ℝ, max (exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K) 0
      = Set.indicator (Set.Ioi (-d2 S0 K r σ T))
        (fun z => exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K) z := by
    intro z
    by_cases hz : z ∈ Set.Ioi (-d2 S0 K r σ T)
    · rw [Set.indicator_of_mem hz]
      have hmem : -d2 S0 K r σ T < z := Set.mem_Ioi.mp hz
      have hexp : exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) > K :=
        (hthresh z).mpr hmem
      have hnonneg : 0 ≤ exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K :=
        le_of_lt (sub_pos.mpr hexp)
      exact max_eq_left hnonneg
    · rw [Set.indicator_of_notMem hz]
      have hle : z ≤ -d2 S0 K r σ T :=
        le_of_not_gt (fun h => hz (Set.mem_Ioi.mpr h))
      have hexp_le : exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) ≤ K := by
        by_contra hcon
        have hgt : K < exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) :=
          not_le.mp hcon
        have := (hthresh z).mp hgt
        linarith
      have hle0 : exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K ≤ 0 :=
        sub_nonpos.mpr hexp_le
      exact max_eq_right hle0
  have hI3 : ∫ z, max (exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K) 0
        ∂(gaussianReal 0 1)
      = ∫ z in Set.Ioi (-d2 S0 K r σ T),
        (exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K)
        ∂(gaussianReal 0 1) := by
    calc ∫ z, max (exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K) 0
            ∂(gaussianReal 0 1)
        = ∫ z, Set.indicator (Set.Ioi (-d2 S0 K r σ T))
            (fun z => exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K) z
            ∂(gaussianReal 0 1) := by
          apply integral_congr_ae
          filter_upwards with z
          exact hpt z
      _ = ∫ z in Set.Ioi (-d2 S0 K r σ T),
            (exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K)
            ∂(gaussianReal 0 1) :=
          integral_indicator measurableSet_Ioi
  have hInt1 : IntegrableOn
        (fun z : ℝ => exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z))
        (Set.Ioi (-d2 S0 K r σ T)) (gaussianReal 0 1) := by
    have h : Integrable (fun z : ℝ => exp ((σ * √T) * z))
        (gaussianReal (0 : ℝ) 1) :=
      integrable_exp_mul_gaussianReal (σ * √T)
    have hrest : IntegrableOn (fun z : ℝ => exp ((σ * √T) * z))
        (Set.Ioi (-d2 S0 K r σ T)) (gaussianReal 0 1) := h.restrict
    have heq : (fun z : ℝ => exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z))
        = (fun z => exp (log S0 + (r - σ ^ 2 / 2) * T) * exp ((σ * √T) * z)) := by
      ext z; rw [exp_add]
    rw [heq]
    exact hrest.const_mul (exp (log S0 + (r - σ ^ 2 / 2) * T))
  have hInt2 : IntegrableOn (fun _ : ℝ => K)
      (Set.Ioi (-d2 S0 K r σ T)) (gaussianReal 0 1) :=
    integrable_const K
  have hsplit : ∫ z in Set.Ioi (-d2 S0 K r σ T),
        (exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) - K)
        ∂(gaussianReal 0 1)
      = (∫ z in Set.Ioi (-d2 S0 K r σ T),
          exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z)
          ∂(gaussianReal 0 1))
        - ∫ _ in Set.Ioi (-d2 S0 K r σ T), K ∂(gaussianReal 0 1) :=
    integral_sub hInt1 hInt2
  have hS0part : ∫ z in Set.Ioi (-d2 S0 K r σ T),
        exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) ∂(gaussianReal 0 1)
      = S0 * exp (r * T) * cdf (gaussianReal 0 1) (d1 S0 K r σ T) := by
    have hpull : ∫ z in Set.Ioi (-d2 S0 K r σ T),
          exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) ∂(gaussianReal 0 1)
        = exp (log S0 + (r - σ ^ 2 / 2) * T)
          * ∫ z in Set.Ioi (-d2 S0 K r σ T), exp ((σ * √T) * z)
            ∂(gaussianReal 0 1) := by
      have hcongr : (∫ z in Set.Ioi (-d2 S0 K r σ T),
            exp ((log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) * z) ∂(gaussianReal 0 1))
          = ∫ z in Set.Ioi (-d2 S0 K r σ T),
            exp (log S0 + (r - σ ^ 2 / 2) * T) * exp ((σ * √T) * z)
            ∂(gaussianReal 0 1) := by
        apply setIntegral_congr_ae measurableSet_Ioi
        filter_upwards with z hz
        rw [exp_add]
      rw [hcongr, ← integral_const_mul]
    rw [hpull]
    have h2 := setIntegral_Ioi_exp_mul_gaussianReal (σ * √T) (-d2 S0 K r σ T)
    rw [h2]
    have hd1 : (σ * √T) - (-d2 S0 K r σ T) = d1 S0 K r σ T := by
      simp only [d2]
      ring
    rw [hd1]
    have hexp : exp (log S0 + (r - σ ^ 2 / 2) * T) * exp ((σ * √T) ^ 2 / 2)
        = S0 * exp (r * T) := by
      rw [← exp_add]
      have harg : (log S0 + (r - σ ^ 2 / 2) * T) + (σ * √T) ^ 2 / 2
          = log S0 + r * T := by
        rw [hsq]
        ring
      rw [harg, exp_add, exp_log hS0]
    calc exp (log S0 + (r - σ ^ 2 / 2) * T)
          * (exp ((σ * √T) ^ 2 / 2) * cdf (gaussianReal 0 1) (d1 S0 K r σ T))
        = (exp (log S0 + (r - σ ^ 2 / 2) * T) * exp ((σ * √T) ^ 2 / 2))
          * cdf (gaussianReal 0 1) (d1 S0 K r σ T) := by ring
      _ = S0 * exp (r * T) * cdf (gaussianReal 0 1) (d1 S0 K r σ T) := by rw [hexp]
  have hKpart : ∫ _ in Set.Ioi (-d2 S0 K r σ T), K ∂(gaussianReal 0 1)
      = K * cdf (gaussianReal 0 1) (d2 S0 K r σ T) := by
    have hneg : (gaussianReal (0 : ℝ) (1 : ℝ≥0)).map (fun x => -x)
        = gaussianReal 0 1 := by
      have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      simpa using h
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi (-d2 S0 K r σ T)
        = Set.Iio (d2 S0 K r σ T) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
      constructor
      · intro h; linarith
      · intro h; linarith
    have hreal : (gaussianReal (0 : ℝ) (1 : ℝ≥0)).real (Set.Ioi (-d2 S0 K r σ T))
        = cdf (gaussianReal 0 1) (d2 S0 K r σ T) := by
      calc (gaussianReal (0 : ℝ) (1 : ℝ≥0)).real (Set.Ioi (-d2 S0 K r σ T))
          = ((gaussianReal (0 : ℝ) (1 : ℝ≥0)).map (fun x => -x)).real
            (Set.Ioi (-d2 S0 K r σ T)) := by rw [hneg]
        _ = (gaussianReal (0 : ℝ) (1 : ℝ≥0)).real
            ((fun x : ℝ => -x) ⁻¹' Set.Ioi (-d2 S0 K r σ T)) := by
            rw [map_measureReal_apply (by fun_prop) measurableSet_Ioi]
        _ = (gaussianReal (0 : ℝ) (1 : ℝ≥0)).real (Set.Iio (d2 S0 K r σ T)) := by
            rw [hpre]
        _ = (gaussianReal (0 : ℝ) (1 : ℝ≥0)).real (Set.Iic (d2 S0 K r σ T)) :=
            measureReal_congr Iio_ae_eq_Iic
        _ = cdf (gaussianReal 0 1) (d2 S0 K r σ T) := (cdf_eq_real _ _).symm
    rw [setIntegral_const, hreal, smul_eq_mul, mul_comm]
  have hI : ∫ x, max (x - K) 0 ∂(riskNeutralLaw S0 r σ T)
      = S0 * exp (r * T) * cdf (gaussianReal 0 1) (d1 S0 K r σ T)
        - K * cdf (gaussianReal 0 1) (d2 S0 K r σ T) := by
    rw [hI1, hI2, hI3, hsplit, hS0part, hKpart]
  rw [hI]
  unfold blackScholesCall
  have hexp1 : exp (-(r * T)) * exp (r * T) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  calc exp (-(r * T))
        * (S0 * exp (r * T) * cdf (gaussianReal 0 1) (d1 S0 K r σ T)
          - K * cdf (gaussianReal 0 1) (d2 S0 K r σ T))
      = S0 * (exp (-(r * T)) * exp (r * T))
          * cdf (gaussianReal 0 1) (d1 S0 K r σ T)
        - K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S0 K r σ T) := by ring
    _ = S0 * cdf (gaussianReal 0 1) (d1 S0 K r σ T)
        - K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S0 K r σ T) := by
        rw [hexp1, mul_one]

end MathlibExt.Probability.Finance.BlackScholes
