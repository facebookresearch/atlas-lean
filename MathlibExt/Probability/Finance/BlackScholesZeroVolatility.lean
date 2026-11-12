/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.BlackScholes
public import MathlibExt.Probability.Distributions.GaussianCdf
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Black-Scholes zero-volatility limit

As `σ → 0+`, the Black-Scholes call price approaches the discounted
deterministic-payoff limit `max (S0 - K e^{-rT}) 0`. The proof cases on the
sign of `A = log (S0 / K) + r T`: if `A > 0`, both `d₁, d₂ → +∞` and
`Φ → 1`; if `A < 0`, both `→ -∞` and `Φ → 0`; if `A = 0`, both `→ 0` and
`Φ → Φ(0) = 1/2`, and `S0 = K e^{-rT}` makes the limit `0` in that case.
This is a limit of the formula function; no stochastic limit theorem is claimed.
The facts `Φ(0) = 1/2` and continuity of the Gaussian cdf are cited from
`MathlibExt.Probability.Distributions.GaussianCdf`, not reproved.

## Main results

* `stdNormal_cdf_zero`: `Φ(0) = 1/2`.
* `tendsto_blackScholesCall_zeroVol`: the zero-volatility limit.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.BlackScholesZeroVolatility

open MeasureTheory ProbabilityTheory Real MathlibExt.Probability.Finance.BlackScholes
open Filter Topology

/-- The standard normal cdf at `0` is `1/2`, cited from
`ProbabilityTheory.cdf_gaussianReal_zero` in
`MathlibExt.Probability.Distributions.GaussianCdf`.
Needed for the at-the-money case of the zero-volatility limit. -/
theorem stdNormal_cdf_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 :=
  ProbabilityTheory.cdf_gaussianReal_zero

/-- Zero-volatility limit (FI17.T04): as `σ → 0+`, the Black-Scholes call price
approaches the discounted deterministic-payoff limit `max (S0 - K e^{-rT}) 0`.
Case on the sign of `A = log (S0 / K) + r T`: if `A > 0`, both `d₁, d₂ → +∞`
and `Φ → 1`; if `A < 0`, both `→ -∞` and `Φ → 0`; if `A = 0`, both `→ 0`
and `Φ → Φ(0) = 1/2`, and `S0 = K e^{-rT}` makes the limit `0` in that case.
Use `tendsto_cdf_atTop` / `tendsto_cdf_atBot` for the infinite cases and
continuity of `Φ` (cited from `ProbabilityTheory.continuous_cdf_gaussianReal`)
for the equality case. No positivity hypothesis on `r` is needed. -/
theorem tendsto_blackScholesCall_zeroVol {S0 K r T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hT : 0 < T) :
    Tendsto (fun σ => blackScholesCall S0 K r σ T) (𝓝[>] 0)
      (𝓝 (max (S0 - K * exp (-(r * T))) 0)) := by
  set A : ℝ := log (S0 / K) + r * T with hA
  have hsqrt : 0 < √T := Real.sqrt_pos.mpr hT
  have hsqrt_ne : √T ≠ 0 := ne_of_gt hsqrt
  have hS0K : 0 < S0 / K := div_pos hS0 hK
  have hsmall : Tendsto (fun σ : ℝ => σ * √T / 2) (𝓝[>] 0) (𝓝 0) := by
    have h := (by continuity : Continuous (fun σ : ℝ => σ * √T / 2)).tendsto 0
    have hm := h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (a := (0 : ℝ)))
    simpa using hm
  have hsmall_neg : Tendsto (fun σ : ℝ => -(σ * √T / 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hsmall.neg
  have hdecomp : ∀ σ : ℝ, σ ≠ 0 → (σ ^ 2 * T / 2) / (σ * √T) = σ * √T / 2 := by
    intro σ hσ
    rw [div_eq_iff (mul_ne_zero hσ hsqrt_ne)]
    have hTT : √T * √T = T := Real.mul_self_sqrt (le_of_lt hT)
    have hring : σ * √T / 2 * (σ * √T) = σ ^ 2 / 2 * (√T * √T) := by ring
    rw [hring, hTT]
    ring
  have hd1eq : ∀ σ : ℝ, σ ≠ 0 → d1 S0 K r σ T = A / (σ * √T) + σ * √T / 2 := by
    intro σ hσ
    have hnum : log (S0 / K) + (r + σ ^ 2 / 2) * T = A + σ ^ 2 * T / 2 := by
      rw [hA]; ring
    change (log (S0 / K) + (r + σ ^ 2 / 2) * T) / (σ * √T)
      = A / (σ * √T) + σ * √T / 2
    rw [hnum, add_div, hdecomp σ hσ]
  have hd2eq : ∀ σ : ℝ, σ ≠ 0
      → d2 S0 K r σ T = A / (σ * √T) + -(σ * √T / 2) := by
    intro σ hσ
    change d1 S0 K r σ T - σ * √T = A / (σ * √T) + -(σ * √T / 2)
    rw [hd1eq σ hσ]
    ring
  have heq1 : (fun σ : ℝ => A / (σ * √T) + σ * √T / 2) =ᶠ[𝓝[>] 0]
      (fun σ : ℝ => d1 S0 K r σ T) :=
    eventually_of_mem self_mem_nhdsWithin
      (fun σ hσ => (hd1eq σ (ne_of_gt (Set.mem_Ioi.mp hσ))).symm)
  have heq2 : (fun σ : ℝ => A / (σ * √T) + -(σ * √T / 2)) =ᶠ[𝓝[>] 0]
      (fun σ : ℝ => d2 S0 K r σ T) :=
    eventually_of_mem self_mem_nhdsWithin
      (fun σ hσ => (hd2eq σ (ne_of_gt (Set.mem_Ioi.mp hσ))).symm)
  have hApos : 0 < A → 0 < S0 - K * exp (-(r * T)) := by
    intro hA0
    rw [hA] at hA0
    have hlog : -(r * T) < log (S0 / K) := by linarith
    have hexp : exp (-(r * T)) < S0 / K := (lt_log_iff_exp_lt hS0K).mp hlog
    have hlt : exp (-(r * T)) * K < S0 := (lt_div_iff₀ hK).mp hexp
    linarith
  have hAneg : A < 0 → S0 - K * exp (-(r * T)) < 0 := by
    intro hA0
    rw [hA] at hA0
    have hlog : log (S0 / K) < -(r * T) := by linarith
    have hexp : exp (log (S0 / K)) < exp (-(r * T)) := Real.exp_lt_exp.mpr hlog
    rw [Real.exp_log hS0K] at hexp
    have hlt : S0 < exp (-(r * T)) * K := (div_lt_iff₀ hK).mp hexp
    linarith
  have hAeq : A = 0 → S0 = K * exp (-(r * T)) := by
    intro hA0
    rw [hA] at hA0
    have hlog : log (S0 / K) = -(r * T) := by linarith
    have hexp : exp (log (S0 / K)) = exp (-(r * T)) := by rw [hlog]
    rw [Real.exp_log hS0K] at hexp
    have hmul : S0 = exp (-(r * T)) * K := (div_eq_iff hK.ne').mp hexp
    linear_combination hmul
  have heqA : (fun σ : ℝ => (A / √T) * σ⁻¹) =ᶠ[𝓝[>] 0]
      (fun σ : ℝ => A / (σ * √T)) :=
    Eventually.of_forall (fun σ => by
      simp only [div_eq_mul_inv, mul_inv]
      ring)
  rcases lt_trichotomy A 0 with hAlt | hAeq0 | hAgt
  · have hC : A / √T < 0 := div_neg_of_neg_of_pos hAlt hsqrt
    have hmain : Tendsto (fun σ : ℝ => (A / √T) * σ⁻¹) (𝓝[>] 0) atBot :=
      Filter.Tendsto.neg_mul_atTop hC tendsto_const_nhds tendsto_inv_nhdsGT_zero
    have hA_bot : Tendsto (fun σ : ℝ => A / (σ * √T)) (𝓝[>] 0) atBot :=
      Filter.Tendsto.congr' heqA hmain
    have hd1_bot : Tendsto (fun σ : ℝ => d1 S0 K r σ T) (𝓝[>] 0) atBot :=
      Filter.Tendsto.congr' heq1 (hA_bot.atBot_add hsmall)
    have hd2_bot : Tendsto (fun σ : ℝ => d2 S0 K r σ T) (𝓝[>] 0) atBot :=
      Filter.Tendsto.congr' heq2 (hA_bot.atBot_add hsmall_neg)
    have hphi1 : Tendsto (fun σ : ℝ => cdf (gaussianReal 0 1) (d1 S0 K r σ T))
        (𝓝[>] 0) (𝓝 0) := by
      simpa [Function.comp_def] using (tendsto_cdf_atBot _).comp hd1_bot
    have hphi2 : Tendsto (fun σ : ℝ => cdf (gaussianReal 0 1) (d2 S0 K r σ T))
        (𝓝[>] 0) (𝓝 0) := by
      simpa [Function.comp_def] using (tendsto_cdf_atBot _).comp hd2_bot
    have hneg : S0 - K * exp (-(r * T)) < 0 := hAneg hAlt
    have hlim : S0 * 0 - (K * exp (-(r * T))) * 0
        = max (S0 - K * exp (-(r * T))) 0 := by
      rw [max_eq_right (le_of_lt hneg)]
      ring
    have hprice : Tendsto
        (fun σ : ℝ => S0 * cdf (gaussianReal 0 1) (d1 S0 K r σ T)
          - K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S0 K r σ T))
        (𝓝[>] 0) (𝓝 (S0 * 0 - (K * exp (-(r * T))) * 0)) :=
      (tendsto_const_nhds.mul hphi1).sub
        ((tendsto_const_nhds (x := K * exp (-(r * T)))).mul hphi2)
    rw [hlim] at hprice
    exact hprice
  · have hSeq : S0 = K * exp (-(r * T)) := hAeq hAeq0
    have hA0div : ∀ σ : ℝ, A / (σ * √T) = 0 := fun σ => by
      rw [hAeq0]; exact zero_div _
    have hd1_zero : Tendsto (fun σ : ℝ => d1 S0 K r σ T) (𝓝[>] 0) (𝓝 0) := by
      have hdecomp0 : Tendsto (fun σ : ℝ => A / (σ * √T) + σ * √T / 2) (𝓝[>] 0)
          (𝓝 0) := by
        have heq0 : (fun σ : ℝ => σ * √T / 2) =ᶠ[𝓝[>] 0]
            (fun σ : ℝ => A / (σ * √T) + σ * √T / 2) :=
          Eventually.of_forall (fun σ => by
            change σ * √T / 2 = A / (σ * √T) + σ * √T / 2
            rw [hA0div σ]; ring)
        exact Filter.Tendsto.congr' heq0 hsmall
      exact Filter.Tendsto.congr' heq1 hdecomp0
    have hd2_zero : Tendsto (fun σ : ℝ => d2 S0 K r σ T) (𝓝[>] 0) (𝓝 0) := by
      have hdecomp0 : Tendsto (fun σ : ℝ => A / (σ * √T) + -(σ * √T / 2))
          (𝓝[>] 0) (𝓝 0) := by
        have heq0 : (fun σ : ℝ => -(σ * √T / 2)) =ᶠ[𝓝[>] 0]
            (fun σ : ℝ => A / (σ * √T) + -(σ * √T / 2)) :=
          Eventually.of_forall (fun σ => by
            change -(σ * √T / 2) = A / (σ * √T) + -(σ * √T / 2)
            rw [hA0div σ]; ring)
        exact Filter.Tendsto.congr' heq0 hsmall_neg
      exact Filter.Tendsto.congr' heq2 hdecomp0
    have hphi1 : Tendsto (fun σ : ℝ => cdf (gaussianReal 0 1) (d1 S0 K r σ T))
        (𝓝[>] 0) (𝓝 (cdf (gaussianReal 0 1) 0)) := by
      simpa [Function.comp_def] using
        (ProbabilityTheory.continuous_cdf_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
          (show (1 : NNReal) ≠ 0 from one_ne_zero)).continuousAt.tendsto.comp hd1_zero
    have hphi2 : Tendsto (fun σ : ℝ => cdf (gaussianReal 0 1) (d2 S0 K r σ T))
        (𝓝[>] 0) (𝓝 (cdf (gaussianReal 0 1) 0)) := by
      simpa [Function.comp_def] using
        (ProbabilityTheory.continuous_cdf_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
          (show (1 : NNReal) ≠ 0 from one_ne_zero)).continuousAt.tendsto.comp hd2_zero
    have hmax : max (S0 - K * exp (-(r * T))) 0 = 0 := by
      have hsub : S0 - K * exp (-(r * T)) = 0 := sub_eq_zero.mpr hSeq
      rw [hsub]
      exact max_eq_right le_rfl
    have hlim : S0 * cdf (gaussianReal 0 1) 0
        - (K * exp (-(r * T))) * cdf (gaussianReal 0 1) 0
        = max (S0 - K * exp (-(r * T))) 0 := by
      rw [hmax]
      linear_combination cdf (gaussianReal 0 1) 0 * hSeq
    have hprice : Tendsto
        (fun σ : ℝ => S0 * cdf (gaussianReal 0 1) (d1 S0 K r σ T)
          - K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S0 K r σ T))
        (𝓝[>] 0) (𝓝 (S0 * cdf (gaussianReal 0 1) 0
          - (K * exp (-(r * T))) * cdf (gaussianReal 0 1) 0)) :=
      (tendsto_const_nhds.mul hphi1).sub
        ((tendsto_const_nhds (x := K * exp (-(r * T)))).mul hphi2)
    rw [hlim] at hprice
    exact hprice
  · have hC : 0 < A / √T := div_pos hAgt hsqrt
    have hmain : Tendsto (fun σ : ℝ => (A / √T) * σ⁻¹) (𝓝[>] 0) atTop :=
      Filter.Tendsto.const_mul_atTop hC tendsto_inv_nhdsGT_zero
    have hA_top : Tendsto (fun σ : ℝ => A / (σ * √T)) (𝓝[>] 0) atTop :=
      Filter.Tendsto.congr' heqA hmain
    have hd1_top : Tendsto (fun σ : ℝ => d1 S0 K r σ T) (𝓝[>] 0) atTop :=
      Filter.Tendsto.congr' heq1 (hA_top.atTop_add hsmall)
    have hd2_top : Tendsto (fun σ : ℝ => d2 S0 K r σ T) (𝓝[>] 0) atTop :=
      Filter.Tendsto.congr' heq2 (hA_top.atTop_add hsmall_neg)
    have hphi1 : Tendsto (fun σ : ℝ => cdf (gaussianReal 0 1) (d1 S0 K r σ T))
        (𝓝[>] 0) (𝓝 1) := by
      simpa [Function.comp_def] using (tendsto_cdf_atTop _).comp hd1_top
    have hphi2 : Tendsto (fun σ : ℝ => cdf (gaussianReal 0 1) (d2 S0 K r σ T))
        (𝓝[>] 0) (𝓝 1) := by
      simpa [Function.comp_def] using (tendsto_cdf_atTop _).comp hd2_top
    have hpos : 0 < S0 - K * exp (-(r * T)) := hApos hAgt
    have hlim : S0 * 1 - (K * exp (-(r * T))) * 1
        = max (S0 - K * exp (-(r * T))) 0 := by
      rw [max_eq_left (le_of_lt hpos)]
      ring
    have hprice : Tendsto
        (fun σ : ℝ => S0 * cdf (gaussianReal 0 1) (d1 S0 K r σ T)
          - K * exp (-(r * T)) * cdf (gaussianReal 0 1) (d2 S0 K r σ T))
        (𝓝[>] 0) (𝓝 (S0 * 1 - (K * exp (-(r * T))) * 1)) :=
      (tendsto_const_nhds.mul hphi1).sub
        ((tendsto_const_nhds (x := K * exp (-(r * T)))).mul hphi2)
    rw [hlim] at hprice
    exact hprice

end MathlibExt.Probability.Finance.BlackScholesZeroVolatility
