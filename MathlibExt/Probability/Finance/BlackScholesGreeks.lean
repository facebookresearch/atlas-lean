/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.BlackScholes
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Black-Scholes delta and positive vega

On `S0, K, T, σ > 0`, the Black-Scholes call price has delta `Φ(d₁)` and
positive vega `S0 φ(d₁) √T`. This is the run's new-result gap: Mathlib has no
derivative of the Gaussian cdf, so `Φ' = φ` is proved here from the integral
representation of the cdf and the fundamental theorem of calculus; the density
identity `S0 φ(d₁) = K e^{-rT} φ(d₂)` then cancels the density terms in both
chain-rule computations.

## Main results

* `hasDerivAt_stdNormal_cdf`: the derivative of the standard normal cdf is the
  standard normal density.
* `blackScholes_phi_identity`: `S0 φ(d₁) = K e^{-rT} φ(d₂)`.
* `blackScholesDelta`, `blackScholesVega`: the delta and vega.
* `hasDerivAt_blackScholesCall_S0`: delta is the `S0`-derivative of the call price.
* `hasDerivAt_blackScholesCall_sigma`: vega is the `σ`-derivative of the call price.
* `blackScholes_vega_pos`: vega is strictly positive.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.BlackScholesGreeks

open MeasureTheory ProbabilityTheory Real MathlibExt.Probability.Finance.BlackScholes

/-- The Black-Scholes delta: `Φ(d₁)`, the sensitivity of the call price to the
spot price `S0`. -/
noncomputable def blackScholesDelta (S0 K r σ T : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) (d1 S0 K r σ T)

/-- The Black-Scholes vega: `S0 φ(d₁) √T`, the sensitivity of the call price to
the volatility `σ`, with `φ` the standard normal density. -/
noncomputable def blackScholesVega (S0 K r σ T : ℝ) : ℝ :=
  S0 * gaussianPDFReal 0 1 (d1 S0 K r σ T) * √T

open intervalIntegral Set

private theorem hasDerivAt_d1_S0 (S0 K r σ T : ℝ) (hS0 : 0 < S0) (hK : 0 < K) :
    HasDerivAt (fun S => d1 S K r σ T) ((1 / S0) / (σ * √T)) S0 := by
  have hKne : K ≠ 0 := ne_of_gt hK
  have hS0ne : S0 ≠ 0 := ne_of_gt hS0
  have hSK : S0 / K ≠ 0 := div_ne_zero hS0ne hKne
  have hdiv : HasDerivAt (fun S : ℝ => S / K) (1 / K) S0 := by
    simpa using (hasDerivAt_id' S0).div_const K
  have heq : (1 / K) / (S0 / K) = 1 / S0 := by
    field_simp
  have hlog : HasDerivAt (fun S : ℝ => log (S / K)) (1 / S0) S0 := by
    have h := hdiv.log hSK
    rwa [heq] at h
  have hnum : HasDerivAt (fun S : ℝ => log (S / K) + (r + σ ^ 2 / 2) * T) (1 / S0) S0 :=
    hlog.add_const _
  have hd : HasDerivAt (fun S : ℝ => (log (S / K) + (r + σ ^ 2 / 2) * T) / (σ * √T))
      ((1 / S0) / (σ * √T)) S0 :=
    hnum.div_const _
  simpa [d1] using hd

private theorem hasDerivAt_d2_S0 (S0 K r σ T : ℝ) (hS0 : 0 < S0) (hK : 0 < K) :
    HasDerivAt (fun S => d2 S K r σ T) ((1 / S0) / (σ * √T)) S0 := by
  have h : HasDerivAt (fun S => d1 S K r σ T) ((1 / S0) / (σ * √T)) S0 :=
    hasDerivAt_d1_S0 S0 K r σ T hS0 hK
  simpa [d2] using h.sub_const (σ * √T)

private theorem exists_hasDerivAt_d1_sigma (S0 K r σ T : ℝ) (hσ : 0 < σ) (hT : 0 < T) :
    ∃ d1', HasDerivAt (fun s => d1 S0 K r s T) d1' σ := by
  have hs2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * σ) σ := by
    simpa using hasDerivAt_pow 2 σ
  have hdiv2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) ((2 * σ) / 2) σ :=
    hs2.div_const 2
  have hadd : HasDerivAt (fun s : ℝ => r + s ^ 2 / 2) ((2 * σ) / 2) σ :=
    hdiv2.const_add r
  have hmulT : HasDerivAt (fun s : ℝ => (r + s ^ 2 / 2) * T) (((2 * σ) / 2) * T) σ :=
    hadd.mul_const T
  have hN : HasDerivAt (fun s : ℝ => log (S0 / K) + (r + s ^ 2 / 2) * T) (((2 * σ) / 2) * T) σ :=
    hmulT.const_add (log (S0 / K))
  have hD : HasDerivAt (fun s : ℝ => s * √T) (√T) σ := by
    simpa using (hasDerivAt_id' σ).mul_const (√T)
  have hDne : σ * √T ≠ 0 :=
    mul_ne_zero (ne_of_gt hσ) (Real.sqrt_ne_zero'.mpr hT)
  have hdiv := hN.div hD hDne
  refine ⟨(((2 * σ) / 2 * T) * (σ * √T)
      - (log (S0 / K) + (r + σ ^ 2 / 2) * T) * √T) / (σ * √T) ^ 2, ?_⟩
  simpa [d1, Pi.div_def] using hdiv

/-- Derivative of the standard normal cdf (FI17.T03, new result): `Φ' = φ`.
Mathlib has no derivative of the Gaussian cdf; prove it in-file from the
integral representation of the cdf and FTC (`intervalIntegral.integral_hasDerivAt_right`),
using continuity of `gaussianPDFReal`. -/
theorem hasDerivAt_stdNormal_cdf (x : ℝ) :
    HasDerivAt (fun y => cdf (gaussianReal 0 1) y) (gaussianPDFReal 0 1 x) x := by
  have hcont : Continuous (gaussianPDFReal 0 1) := by
    unfold gaussianPDFReal
    fun_prop
  have hcdf : ∀ y : ℝ, cdf (gaussianReal 0 1) y
      = ∫ t in Iic y, gaussianPDFReal 0 1 t := by
    intro y
    rw [cdf_eq_real, measureReal_def]
    rw [gaussianReal_apply_eq_integral 0 (by simp) (Iic y)]
    rw [ENNReal.toReal_ofReal]
    apply setIntegral_nonneg measurableSet_Iic
    intro a _
    exact gaussianPDFReal_nonneg _ _ _
  have hIic : ∀ y : ℝ, (∫ t in Iic y, gaussianPDFReal 0 1 t)
      = (∫ t in Iic (0:ℝ), gaussianPDFReal 0 1 t)
        + ∫ t in (0:ℝ)..y, gaussianPDFReal 0 1 t := by
    intro y
    have h := integral_Iic_sub_Iic
      (f := gaussianPDFReal 0 1) (μ := volume)
      (a := (0:ℝ)) (b := y)
      ((integrable_gaussianPDFReal _ _).integrableOn)
      ((integrable_gaussianPDFReal _ _).integrableOn)
    have h' : (∫ t in Iic y, gaussianPDFReal 0 1 t)
        = (∫ t in (0:ℝ)..y, gaussianPDFReal 0 1 t)
          + (∫ t in Iic (0:ℝ), gaussianPDFReal 0 1 t) := by
      rw [← h]; ring
    rw [h']; ring
  have hFTC : HasDerivAt (fun y => ∫ t in (0:ℝ)..y, gaussianPDFReal 0 1 t)
      (gaussianPDFReal 0 1 x) x :=
    integral_hasDerivAt_right
      (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _)
      (hcont.continuousAt)
  have hAdd : HasDerivAt
      (fun y => (∫ t in Iic (0:ℝ), gaussianPDFReal 0 1 t)
        + ∫ t in (0:ℝ)..y, gaussianPDFReal 0 1 t)
      (gaussianPDFReal 0 1 x) x :=
    hFTC.const_add (∫ t in Iic (0:ℝ), gaussianPDFReal 0 1 t)
  have heq : (fun y => cdf (gaussianReal 0 1) y)
      = (fun y => (∫ t in Iic (0:ℝ), gaussianPDFReal 0 1 t)
        + ∫ t in (0:ℝ)..y, gaussianPDFReal 0 1 t) := by
    funext y
    rw [hcdf y, hIic y]
  rw [heq]
  exact hAdd

/-- Density identity (FI17.T03): `S0 φ(d₁) = K e^{-rT} φ(d₂)`. Algebra from
`d₁² - d₂² = 2 log (S0 / K) + 2 r T` and the explicit Gaussian density; needs
`S0, K > 0` for the logarithm. -/
theorem blackScholes_phi_identity {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) :
    S0 * gaussianPDFReal 0 1 (d1 S0 K r σ T) =
      K * exp (-(r * T)) * gaussianPDFReal 0 1 (d2 S0 K r σ T) := by
  have hTnn : 0 ≤ T := le_of_lt hT
  have hsqrt : (√T) ^ 2 = T := Real.sq_sqrt hTnn
  have hD2 : (σ * √T) ^ 2 = σ ^ 2 * T := by
    rw [mul_pow, hsqrt]
  have hd1D : d1 S0 K r σ T * (σ * √T)
      = log (S0 / K) + (r + σ ^ 2 / 2) * T := by
    unfold d1
    have hD : σ * √T ≠ 0 := mul_ne_zero (ne_of_gt hσ) (Real.sqrt_ne_zero'.mpr hT)
    field_simp
  have hd2 : d2 S0 K r σ T = d1 S0 K r σ T - σ * √T := rfl
  have hsq : (d1 S0 K r σ T) ^ 2 - (d2 S0 K r σ T) ^ 2
      = 2 * log (S0 / K) + 2 * r * T := by
    have hsq2 : (d1 S0 K r σ T) ^ 2 - (d2 S0 K r σ T) ^ 2
        = 2 * (d1 S0 K r σ T * (σ * √T)) - (σ * √T) ^ 2 := by
      rw [hd2]; ring
    rw [hsq2, hd1D, hD2]
    ring
  have hlog : log (S0 / K) = log S0 - log K := Real.log_div (ne_of_gt hS0) (ne_of_gt hK)
  set a := d1 S0 K r σ T with ha
  set b := d2 S0 K r σ T with hb
  have hsq' : a ^ 2 - b ^ 2 = 2 * log (S0 / K) + 2 * r * T := hsq
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, sub_zero, mul_one]
  suffices hsuff : S0 * exp (-a ^ 2 / 2) = K * exp (-(r * T)) * exp (-b ^ 2 / 2) by
    calc S0 * ((√(2 * π))⁻¹ * exp (-a ^ 2 / 2))
        = (√(2 * π))⁻¹ * (S0 * exp (-a ^ 2 / 2)) := by ring
      _ = (√(2 * π))⁻¹ * (K * exp (-(r * T)) * exp (-b ^ 2 / 2)) := by rw [hsuff]
      _ = K * exp (-(r * T)) * ((√(2 * π))⁻¹ * exp (-b ^ 2 / 2)) := by ring
  have hS0exp : S0 = exp (log S0) := (Real.exp_log hS0).symm
  have hKexp : K = exp (log K) := (Real.exp_log hK).symm
  rw [hS0exp, hKexp]
  have e1 : exp (log S0) * exp (-a ^ 2 / 2) = exp (log S0 + -a ^ 2 / 2) := by
    rw [← Real.exp_add]
  have e2 : exp (log K) * exp (-(r * T)) * exp (-b ^ 2 / 2)
      = exp (log K + (-(r * T) + -b ^ 2 / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e1, e2]
  congr 1
  rw [hlog] at hsq'
  linarith

/-- Delta (FI17.T03): the derivative of the Black-Scholes call price with
respect to `S0` is `Φ(d₁)`. Chain rule through `d₁` and `d₂`: both have the
same `S0`-derivative `1 / (S0 σ √T)`, so the density terms cancel by the
identity above. -/
theorem hasDerivAt_blackScholesCall_S0 {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) :
    HasDerivAt (fun S => blackScholesCall S K r σ T)
      (blackScholesDelta S0 K r σ T) S0 := by
  have hd1 := hasDerivAt_d1_S0 S0 K r σ T hS0 hK
  have hd2 := hasDerivAt_d2_S0 S0 K r σ T hS0 hK
  have hPhi1 : HasDerivAt (fun S => cdf (gaussianReal 0 1) (d1 S K r σ T))
      (gaussianPDFReal 0 1 (d1 S0 K r σ T) * ((1 / S0) / (σ * √T))) S0 :=
    (hasDerivAt_stdNormal_cdf (d1 S0 K r σ T)).comp S0 hd1
  have hPhi2 : HasDerivAt (fun S => cdf (gaussianReal 0 1) (d2 S K r σ T))
      (gaussianPDFReal 0 1 (d2 S0 K r σ T) * ((1 / S0) / (σ * √T))) S0 :=
    (hasDerivAt_stdNormal_cdf (d2 S0 K r σ T)).comp S0 hd2
  have hId : HasDerivAt (fun S : ℝ => S) 1 S0 := hasDerivAt_id' S0
  have hTerm1 : HasDerivAt (fun S => S * cdf (gaussianReal 0 1) (d1 S K r σ T))
      (1 * cdf (gaussianReal 0 1) (d1 S0 K r σ T)
        + S0 * (gaussianPDFReal 0 1 (d1 S0 K r σ T) * ((1 / S0) / (σ * √T)))) S0 :=
    hId.mul hPhi1
  have hTerm2 : HasDerivAt (fun S => K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S K r σ T))
      (K * exp (-(r * T)) * (gaussianPDFReal 0 1 (d2 S0 K r σ T) * ((1 / S0) / (σ * √T)))) S0 :=
    hPhi2.const_mul _
  have hCall : HasDerivAt
      (fun S => S * cdf (gaussianReal 0 1) (d1 S K r σ T)
        - K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S K r σ T))
      ((1 * cdf (gaussianReal 0 1) (d1 S0 K r σ T)
        + S0 * (gaussianPDFReal 0 1 (d1 S0 K r σ T) * ((1 / S0) / (σ * √T))))
        - K * exp (-(r * T)) * (gaussianPDFReal 0 1 (d2 S0 K r σ T) * ((1 / S0) / (σ * √T)))) S0 :=
    hTerm1.sub hTerm2
  have hexpr : (1 * cdf (gaussianReal 0 1) (d1 S0 K r σ T)
        + S0 * (gaussianPDFReal 0 1 (d1 S0 K r σ T) * ((1 / S0) / (σ * √T))))
        - K * exp (-(r * T)) * (gaussianPDFReal 0 1 (d2 S0 K r σ T) * ((1 / S0) / (σ * √T)))
      = blackScholesDelta S0 K r σ T := by
    unfold blackScholesDelta
    have hident : S0 * gaussianPDFReal 0 1 (d1 S0 K r σ T) =
        K * exp (-(r * T)) * gaussianPDFReal 0 1 (d2 S0 K r σ T) :=
      blackScholes_phi_identity hS0 hK hσ hT
    linear_combination ((1 / S0) / (σ * √T)) * hident
  rw [hexpr] at hCall
  simpa [blackScholesCall] using hCall

/-- Vega (FI17.T03): the derivative of the Black-Scholes call price with
respect to `σ` is `S0 φ(d₁) √T`. Chain rule: `d₂ = d₁ - σ √T`, so its
`σ`-derivative is the `d₁`-derivative minus `√T`; the density terms cancel
by the identity above, leaving `K e^{-rT} φ(d₂) √T = S0 φ(d₁) √T`. -/
theorem hasDerivAt_blackScholesCall_sigma {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) :
    HasDerivAt (fun s => blackScholesCall S0 K r s T)
      (blackScholesVega S0 K r σ T) σ := by
  obtain ⟨d1', hd1⟩ := exists_hasDerivAt_d1_sigma S0 K r σ T hσ hT
  have hD : HasDerivAt (fun s : ℝ => s * √T) (√T) σ := by
    simpa using (hasDerivAt_id' σ).mul_const (√T)
  have hd2 : HasDerivAt (fun s => d2 S0 K r s T) (d1' - √T) σ := hd1.sub hD
  have hPhi1 : HasDerivAt (fun s => cdf (gaussianReal 0 1) (d1 S0 K r s T))
      (gaussianPDFReal 0 1 (d1 S0 K r σ T) * d1') σ :=
    (hasDerivAt_stdNormal_cdf (d1 S0 K r σ T)).comp σ hd1
  have hPhi2 : HasDerivAt (fun s => cdf (gaussianReal 0 1) (d2 S0 K r s T))
      (gaussianPDFReal 0 1 (d2 S0 K r σ T) * (d1' - √T)) σ :=
    (hasDerivAt_stdNormal_cdf (d2 S0 K r σ T)).comp σ hd2
  have hTerm1 : HasDerivAt (fun s => S0 * cdf (gaussianReal 0 1) (d1 S0 K r s T))
      (S0 * (gaussianPDFReal 0 1 (d1 S0 K r σ T) * d1')) σ :=
    hPhi1.const_mul S0
  have hTerm2 : HasDerivAt (fun s => K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S0 K r s T))
      (K * exp (-(r * T)) * (gaussianPDFReal 0 1 (d2 S0 K r σ T) * (d1' - √T))) σ :=
    hPhi2.const_mul _
  have hCall : HasDerivAt
      (fun s => S0 * cdf (gaussianReal 0 1) (d1 S0 K r s T)
        - K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S0 K r s T))
      (S0 * (gaussianPDFReal 0 1 (d1 S0 K r σ T) * d1')
        - K * exp (-(r * T)) * (gaussianPDFReal 0 1 (d2 S0 K r σ T) * (d1' - √T))) σ :=
    hTerm1.sub hTerm2
  have hexpr : S0 * (gaussianPDFReal 0 1 (d1 S0 K r σ T) * d1')
        - K * exp (-(r * T)) * (gaussianPDFReal 0 1 (d2 S0 K r σ T) * (d1' - √T))
      = blackScholesVega S0 K r σ T := by
    unfold blackScholesVega
    have hident : S0 * gaussianPDFReal 0 1 (d1 S0 K r σ T) =
        K * exp (-(r * T)) * gaussianPDFReal 0 1 (d2 S0 K r σ T) :=
      blackScholes_phi_identity hS0 hK hσ hT
    linear_combination (d1' - √T) * hident
  rw [hexpr] at hCall
  simpa [blackScholesCall] using hCall

/-- Positive vega (FI17.T03): vega is strictly positive on `S0, K, σ, T > 0`,
since the Gaussian density is strictly positive and `S0 √T > 0`. -/
theorem blackScholes_vega_pos {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) :
    0 < blackScholesVega S0 K r σ T := by
  unfold blackScholesVega
  apply mul_pos
  · apply mul_pos hS0
    exact gaussianPDFReal_pos _ _ _ (by simp)
  · exact Real.sqrt_pos.mpr hT

end MathlibExt.Probability.Finance.BlackScholesGreeks
