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
`max (K e^{-rT} - S0) 0 ≤ P ≤ K e^{-rT}` follow. The lower bounds come from
the discounted-expectation formula `discounted_integral_call_riskNeutralLaw`:
the call price is the discounted expectation of a nonnegative payoff, and the
put price is a discounted call price with `S0` and `K` swapped and `r` negated.
This is a formula-level statement; no continuous-trading replication is
claimed.

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
  rw [← discounted_integral_call_riskNeutralLaw hS0 hK hσ hT]
  exact mul_nonneg (exp_pos _).le (integral_nonneg fun x => le_max_right _ _)

private theorem blackScholesPut_nonneg {S0 K r σ T : ℝ} (hS0 : 0 < S0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) : 0 ≤ blackScholesPut S0 K r σ T := by
  have hC := blackScholesCall_nonneg (S0 := K) (K := S0) (r := -r) hK hS0 hσ hT
  have hid : blackScholesPut S0 K r σ T
      = exp (-(r * T)) * blackScholesCall K S0 (-r) σ T := by
    have hexpT : -((-r) * T) = r * T := by ring
    have hexp1 : exp (-(r * T)) * exp (r * T) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simp only [blackScholesCall, blackScholesPut]
    rw [d1_swap hS0 hK hσ hT, d2_swap hS0 hK hσ hT, hexpT]
    linear_combination (S0 * cdf (gaussianReal 0 1) (-d1 S0 K r σ T)) * hexp1
  rw [hid]
  exact mul_nonneg (exp_pos _).le hC

/-- Put-call parity (FI17.T02): `C - P = S0 - K e^{-rT}`. Pure algebra from the
symmetry `cdf_gaussianReal_neg`; no positivity hypothesis is needed. -/
theorem blackScholes_putCallParity (S0 K r σ T : ℝ) :
    blackScholesCall S0 K r σ T - blackScholesPut S0 K r σ T =
      S0 - K * exp (-(r * T)) := by
  unfold blackScholesCall blackScholesPut
  rw [cdf_gaussianReal_neg, cdf_gaussianReal_neg]
  ring

/-- Static bounds for the call (FI17.T02): `max (S0 - K e^{-rT}) 0 ≤ C ≤ S0`.
The upper bound is algebra from `0 ≤ Φ ≤ 1`. The lower bound `0 ≤ C` holds
because `C` is the discounted expectation of the nonnegative payoff
`max (x - K) 0` (`discounted_integral_call_riskNeutralLaw`); the lower bound
`S0 - K e^{-rT} ≤ C` is put nonnegativity through parity, and
`P(S0, K, r) = e^{-rT} C(K, S0, -r)` reduces put nonnegativity to call
nonnegativity. -/
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
