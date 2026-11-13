/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.BlackScholes
public import Mathlib.Probability.Distributions.Gaussian.Real
import MathlibExt.Probability.Distributions.GaussianCdf

/-!
# Black-Scholes put-call parity and static bounds

The Black-Scholes formula satisfies put-call parity and the model's static
bounds. The put price is defined by the formula
`P = K e^{-rT} Φ(-d₂) - S0 Φ(-d₁)`; parity `C - P = S0 - K e^{-rT}` is pure
algebra from the symmetry `Φ(-x) = 1 - Φ(x)`, and the call bounds
`max (S0 - K e^{-rT}) 0 ≤ C ≤ S0` and put bounds
`max (K e^{-rT} - S0) 0 ≤ P ≤ K e^{-rT}` follow. The lower bound is proved by
a density-shift comparison, not by an expectation argument. This is a
formula-level statement; no continuous-trading replication is claimed.

## Main results

* `blackScholesPut`: the Black-Scholes put price.
* `blackScholes_putCallParity`: put-call parity.
* `blackScholesCall_bounds`, `blackScholesPut_bounds`: the static bounds.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.BlackScholesPutCallParity

open MeasureTheory ProbabilityTheory Real MathlibExt.Probability.Finance.BlackScholes

/-- The Black-Scholes price of a European put with strike `K` and maturity `T`:
`K e^{-rT} Φ(-d₂) - S0 Φ(-d₁)`, with `Φ = cdf (gaussianReal 0 1)`. -/
noncomputable def blackScholesPut (S0 K r σ T : ℝ) : ℝ :=
  K * exp (-(r * T)) * cdf (gaussianReal 0 1) (-d2 S0 K r σ T) -
    S0 * cdf (gaussianReal 0 1) (-d1 S0 K r σ T)

private theorem gaussianPDFReal_shift_le {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) (t : ℝ) (ht : t ≤ -d1 S0 K r σ T) :
    (S0 / K) * exp (r * T) * gaussianPDFReal 0 1 t
      ≤ gaussianPDFReal 0 1 (t + σ * √T) := by
  have hsqrtT : 0 < √T := Real.sqrt_pos.mpr hT
  have ha : 0 < σ * √T := mul_pos hσ hsqrtT
  have ha0 : σ * √T ≠ 0 := ne_of_gt ha
  have hsq : (σ * √T) ^ 2 = σ ^ 2 * T := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hT)]
  have hSK : 0 < S0 / K := div_pos hS0 hK
  have had1 : (σ * √T) * d1 S0 K r σ T = log (S0 / K) + (r + σ ^ 2 / 2) * T := by
    simp only [d1]
    rw [mul_div_cancel₀ _ ha0]
  have hkey : log (S0 / K) + r * T ≤ -((σ * √T) * t) - (σ * √T) ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left ht ha.le
    rw [mul_neg] at h
    rw [hsq]
    linarith [had1, h]
  have hexp_le : exp (log (S0 / K) + r * T)
      ≤ exp (-((σ * √T) * t) - (σ * √T) ^ 2 / 2) :=
    exp_le_exp.mpr hkey
  have hc : (S0 / K) * exp (r * T) = exp (log (S0 / K) + r * T) := by
    rw [Real.exp_add, Real.exp_log hSK]
  have hφ : gaussianPDFReal 0 1 (t + σ * √T)
      = gaussianPDFReal 0 1 t * exp (-((σ * √T) * t) - (σ * √T) ^ 2 / 2) := by
    simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  rw [hc, hφ, mul_comm (gaussianPDFReal 0 1 t) _]
  exact mul_le_mul_of_nonneg_right hexp_le (gaussianPDFReal_nonneg 0 1 t)

private theorem blackScholesPut_nonneg {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) : 0 ≤ blackScholesPut S0 K r σ T := by
  have hv1 : (1 : NNReal) ≠ 0 := one_ne_zero
  have hsqrtT : 0 < √T := Real.sqrt_pos.mpr hT
  have ha : 0 < σ * √T := mul_pos hσ hsqrtT
  have hc : 0 < (S0 / K) * exp (r * T) :=
    mul_pos (div_pos hS0 hK) (exp_pos _)
  have hneg : -d2 S0 K r σ T = -d1 S0 K r σ T + σ * √T := by
    simp only [d2]
    ring
  have hφmeas : Measurable (gaussianPDF 0 1) := measurable_gaussianPDF 0 1
  have hIic1 : MeasurableSet (Set.Iic (-d1 S0 K r σ T)) := measurableSet_Iic
  have hIic2 : MeasurableSet (Set.Iic (-d2 S0 K r σ T)) := measurableSet_Iic
  have hFmeas :
      Measurable ((Set.Iic (-d2 S0 K r σ T)).indicator (gaussianPDF 0 1)) :=
    hφmeas.indicator hIic2
  have hF1meas :
      Measurable ((Set.Iic (-d1 S0 K r σ T)).indicator (gaussianPDF 0 1)) :=
    hφmeas.indicator hIic1
  have hpoint : ∀ t : ℝ, t ≤ -d1 S0 K r σ T →
      ENNReal.ofReal ((S0 / K) * exp (r * T)) * gaussianPDF 0 1 t
        ≤ gaussianPDF 0 1 (t + σ * √T) := by
    intro t ht
    have h := gaussianPDFReal_shift_le hS0 hK hσ hT t ht
    simp only [gaussianPDF, ← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal h
  have hpt : ∀ t : ℝ,
      (Set.Iic (-d2 S0 K r σ T)).indicator (gaussianPDF 0 1) (t + σ * √T)
        = (Set.Iic (-d1 S0 K r σ T)).indicator
          (fun t => gaussianPDF 0 1 (t + σ * √T)) t := by
    intro t
    by_cases ht : t ≤ -d1 S0 K r σ T
    · have hmem1 : t + σ * √T ∈ Set.Iic (-d2 S0 K r σ T) := by
        rw [Set.mem_Iic, hneg]
        exact add_le_add_left ht _
      have hmem2 : t ∈ Set.Iic (-d1 S0 K r σ T) := Set.mem_Iic.mpr ht
      rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2]
    · have h2 : t ∉ Set.Iic (-d1 S0 K r σ T) := fun h => ht (Set.mem_Iic.mp h)
      have h1 : t + σ * √T ∉ Set.Iic (-d2 S0 K r σ T) := by
        intro hcon
        apply ht
        have hcon' := Set.mem_Iic.mp hcon
        rw [hneg] at hcon'
        exact le_of_add_le_add_right hcon'
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  have hI2 : (gaussianReal 0 1) (Set.Iic (-d2 S0 K r σ T))
      = ∫⁻ t, (Set.Iic (-d2 S0 K r σ T)).indicator (gaussianPDF 0 1) t ∂volume := by
    rw [gaussianReal_apply 0 hv1, ← lintegral_indicator hIic2]
  have htrans : (∫⁻ t, (Set.Iic (-d2 S0 K r σ T)).indicator (gaussianPDF 0 1) t ∂volume)
      = ∫⁻ t, (Set.Iic (-d2 S0 K r σ T)).indicator (gaussianPDF 0 1) (t + σ * √T)
        ∂volume :=
    ((measurePreserving_add_right volume (σ * √T)).lintegral_comp hFmeas).symm
  have hshift :
      (∫⁻ t, (Set.Iic (-d2 S0 K r σ T)).indicator (gaussianPDF 0 1) (t + σ * √T)
        ∂volume)
        = ∫⁻ t, (Set.Iic (-d1 S0 K r σ T)).indicator
          (fun t => gaussianPDF 0 1 (t + σ * √T)) t ∂volume := by
    simp only [hpt]
  have hmono : (∫⁻ t, (Set.Iic (-d1 S0 K r σ T)).indicator
          (fun t => ENNReal.ofReal ((S0 / K) * exp (r * T)) * gaussianPDF 0 1 t) t
          ∂volume)
        ≤ ∫⁻ t, (Set.Iic (-d1 S0 K r σ T)).indicator
          (fun t => gaussianPDF 0 1 (t + σ * √T)) t ∂volume := by
    refine lintegral_mono_ae (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ Set.Iic (-d1 S0 K r σ T)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      exact hpoint t (Set.mem_Iic.mp ht)
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  have hconst : (∫⁻ t, (Set.Iic (-d1 S0 K r σ T)).indicator
          (fun t => ENNReal.ofReal ((S0 / K) * exp (r * T)) * gaussianPDF 0 1 t) t
          ∂volume)
        = ENNReal.ofReal ((S0 / K) * exp (r * T))
          * (gaussianReal 0 1) (Set.Iic (-d1 S0 K r σ T)) := by
    simp only [Set.indicator_const_mul]
    rw [lintegral_const_mul _ hF1meas, lintegral_indicator hIic1,
      ← gaussianReal_apply 0 hv1]
  have hI : ENNReal.ofReal ((S0 / K) * exp (r * T))
          * (gaussianReal 0 1) (Set.Iic (-d1 S0 K r σ T))
        ≤ (gaussianReal 0 1) (Set.Iic (-d2 S0 K r σ T)) := by
    rw [hI2, htrans, hshift, ← hconst]
    exact hmono
  have hfin1 : (gaussianReal 0 1) (Set.Iic (-d1 S0 K r σ T)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := 1) ?_ ?_
    · simp
    · calc (gaussianReal 0 1) _ ≤ (gaussianReal 0 1) Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  have hfin2 : (gaussianReal 0 1) (Set.Iic (-d2 S0 K r σ T)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := 1) ?_ ?_
    · simp
    · calc (gaussianReal 0 1) _ ≤ (gaussianReal 0 1) Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  have hreal : (S0 / K) * exp (r * T) * cdf (gaussianReal 0 1) (-d1 S0 K r σ T)
      ≤ cdf (gaussianReal 0 1) (-d2 S0 K r σ T) := by
    have h := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin1) hfin2).mpr hI
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at h
    rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def]
    exact h
  have hKe : 0 < K * exp (-(r * T)) := mul_pos hK (exp_pos _)
  have hKK : K * exp (-(r * T)) * ((S0 / K) * exp (r * T)) = S0 := by
    have hK0 : K ≠ 0 := ne_of_gt hK
    have he : exp (-(r * T)) * exp (r * T) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc K * exp (-(r * T)) * ((S0 / K) * exp (r * T))
        = (K * (S0 / K)) * (exp (-(r * T)) * exp (r * T)) := by ring
      _ = S0 * 1 := by rw [he, mul_div_cancel₀ _ hK0]
      _ = S0 := mul_one S0
  have hmul := mul_le_mul_of_nonneg_left hreal hKe.le
  have hsmul : K * exp (-(r * T))
          * ((S0 / K) * exp (r * T) * cdf (gaussianReal 0 1) (-d1 S0 K r σ T))
        = S0 * cdf (gaussianReal 0 1) (-d1 S0 K r σ T) := by
    rw [← mul_assoc, hKK]
  simp only [blackScholesPut]
  linarith [hmul, hsmul]

private theorem d1_swap {S0 K r σ T : ℝ} (_hS0 : 0 < S0) (_hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) :
    d1 K S0 (-r) σ T = -d2 S0 K r σ T := by
  have hsqrtT : 0 < √T := Real.sqrt_pos.mpr hT
  have ha : σ * √T ≠ 0 := ne_of_gt (mul_pos hσ hsqrtT)
  have hsq : (σ * √T) ^ 2 = σ ^ 2 * T := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hT)]
  have hlog : log (K / S0) = -log (S0 / K) := by
    rw [← inv_div, Real.log_inv]
  simp only [d1, d2]
  rw [hlog, div_eq_iff ha, neg_sub, sub_mul, div_mul_cancel₀ _ ha, ← pow_two,
    hsq]
  ring

private theorem d2_swap {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) :
    d2 K S0 (-r) σ T = -d1 S0 K r σ T := by
  simp only [d2]
  rw [d1_swap hS0 hK hσ hT]
  simp only [d2]
  ring

private theorem blackScholesCall_nonneg {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) : 0 ≤ blackScholesCall S0 K r σ T := by
  have hP := blackScholesPut_nonneg (S0 := K) (K := S0) (r := -r) hK hS0 hσ hT
  have hexp : 0 < exp (-(r * T)) := exp_pos _
  have hid : blackScholesCall S0 K r σ T
      = exp (-(r * T)) * blackScholesPut K S0 (-r) σ T := by
    have hexpT : -((-r) * T) = r * T := by ring
    have hexp1 : exp (-(r * T)) * exp (r * T) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simp only [blackScholesCall, blackScholesPut]
    rw [d1_swap hS0 hK hσ hT, d2_swap hS0 hK hσ hT]
    simp only [neg_neg]
    rw [hexpT]
    linear_combination (-(S0 * cdf (gaussianReal 0 1) (d1 S0 K r σ T))) * hexp1
  rw [hid]
  exact mul_nonneg hexp.le hP

/-- Put-call parity (FI17.T02): `C - P = S0 - K e^{-rT}`. Pure algebra from the
symmetry `cdf_gaussianReal_neg`; no positivity hypothesis is needed. -/
theorem blackScholes_putCallParity (S0 K r σ T : ℝ) :
    blackScholesCall S0 K r σ T - blackScholesPut S0 K r σ T =
      S0 - K * exp (-(r * T)) := by
  unfold blackScholesCall blackScholesPut
  rw [cdf_gaussianReal_neg, cdf_gaussianReal_neg]
  ring

/-- Static bounds for the call (FI17.T02): `max (S0 - K e^{-rT}) 0 ≤ C ≤ S0`.
The upper bound is algebra from `0 ≤ Φ ≤ 1`. The lower bound is equivalent to
put nonnegativity; prove it by the density-shift comparison (do NOT cite the
merged FI17.T01 expectation identity — it is not available in the sandbox, and
the density-shift proof below is self-contained): for `t ≤ -d₁`,
`φ(t + σ√T) ≥ (S0 / K) * e^{rT} * φ(t)`, because
`φ(t + a) / φ(t) = exp (-(a * t + a² / 2))` with `a = σ√T`, and
`-a * t - a² / 2 ≥ a * d₁ - a² / 2 = log (S0 / K) + r * T` there. Integrate
over `Iic (-d₁)`: the left side becomes `Φ(-d₂)` (shift the interval), the
right side `(S0 / K) * e^{rT} * Φ(-d₁)`, giving `K e^{-rT} Φ(-d₂) ≥ S0 Φ(-d₁)`. -/
theorem blackScholesCall_bounds {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) :
    max (S0 - K * exp (-(r * T))) 0 ≤ blackScholesCall S0 K r σ T ∧
      blackScholesCall S0 K r σ T ≤ S0 := by
  have hC0 : 0 ≤ blackScholesCall S0 K r σ T :=
    blackScholesCall_nonneg hS0 hK hσ hT
  have hP0 : 0 ≤ blackScholesPut S0 K r σ T :=
    blackScholesPut_nonneg hS0 hK hσ hT
  have hpar := blackScholes_putCallParity S0 K r σ T
  constructor
  · rw [max_le_iff]
    constructor
    · linarith
    · exact hC0
  · have hΦ1 : cdf (gaussianReal 0 1) (d1 S0 K r σ T) ≤ 1 := cdf_le_one _ _
    have hpos :
        0 ≤ K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S0 K r σ T) :=
      mul_nonneg (mul_nonneg (le_of_lt hK) (exp_pos _).le) (cdf_nonneg _ _)
    have hS0Φ : S0 * cdf (gaussianReal 0 1) (d1 S0 K r σ T) ≤ S0 := by
      calc S0 * cdf (gaussianReal 0 1) (d1 S0 K r σ T) ≤ S0 * 1 :=
              mul_le_mul_of_nonneg_left hΦ1 (le_of_lt hS0)
        _ = S0 := mul_one S0
    simp only [blackScholesCall]
    linarith

/-- Static bounds for the put (FI17.T02): `max (K e^{-rT} - S0) 0 ≤ P ≤ K e^{-rT}`.
Consequences of put-call parity plus the call bounds. -/
theorem blackScholesPut_bounds {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) :
    max (K * exp (-(r * T)) - S0) 0 ≤ blackScholesPut S0 K r σ T ∧
      blackScholesPut S0 K r σ T ≤ K * exp (-(r * T)) := by
  have hC : max (S0 - K * exp (-(r * T))) 0 ≤ blackScholesCall S0 K r σ T ∧
      blackScholesCall S0 K r σ T ≤ S0 :=
    blackScholesCall_bounds hS0 hK hσ hT
  have hClo : S0 - K * exp (-(r * T)) ≤ blackScholesCall S0 K r σ T :=
    le_trans (le_max_left _ _) hC.1
  have hC0 : 0 ≤ blackScholesCall S0 K r σ T :=
    le_trans (le_max_right _ _) hC.1
  have hChi : blackScholesCall S0 K r σ T ≤ S0 := hC.2
  have hpar := blackScholes_putCallParity S0 K r σ T
  constructor
  · rw [max_le_iff]
    constructor <;> linarith
  · linarith

end MathlibExt.Probability.Finance.BlackScholesPutCallParity
