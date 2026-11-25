/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The Euler–Lotka equation and the reproductive number

In the renewal model of an epidemic, incidence satisfies `b(t) = R ∫ b(t - a) g(da)`, where
`g` is the law of the generation interval (the time from infection of a case to infection of
the cases it causes) and `R` the mean number of secondary cases (Wallinga–Lipsitch 2007,
eq. 2.1, a renewal equation of Feller 1941). Exponential growth `b(t) = c e^{r t}` at rate
`r` solves the renewal equation exactly when

`R = 1 / M_g(-r)`, `M_g(-r) = ∫ e^{-r a} g(da)` (the Euler–Lotka equation, their eq. 2.9).

Here `M_g` is Mathlib's moment generating function `mgf id g`.

## Main definitions

* `reproductionNumber g r = (M_g(-r))⁻¹`.
* `ConvexOrderLE g₁ g₂`: `g₁` is smaller than `g₂` in the convex order.

## Main results

* `renewal_exp_iff`: `c e^{r t} = R ∫ c e^{r (t - a)} g(da)` for all `t` iff `R M_g(-r) = 1`;
  `renewal_exp_iff_reproductionNumber`: iff `R = reproductionNumber g r`.
* `reproductionNumber_dirac`: a fixed generation interval `T` gives `R = e^{r T}`.
* `reproductionNumber_gammaMeasure`: a gamma generation interval with shape `α` and rate `β`
  gives `R = (1 + r / β)^α` (for `r > -β`); `reproductionNumber_expMeasure`: an exponential
  generation interval with mean `T` gives `R = 1 + r T` (for `r T > -1`).
* `reproductionNumber_le_of_convexOrderLE`: **more spread lowers `R`**: if `g₁ ≤cx g₂`, then
  `R(g₂) ≤ R(g₁)` at the same growth rate `r` (for every real `r`, since `a ↦ e^{-r a}` is
  convex).
* `reproductionNumber_le_exp_mean`: by Jensen, `R ≤ e^{r T̄}` where `T̄` is the mean generation
  interval; the fixed interval attains it, and `1 + r T ≤ e^{r T}` is the exponential case.

All identities hold for every probability measure `g` on `ℝ` with the stated integrability;
generation intervals are nonnegative in the biological model, which no statement here needs.
These two closed forms correct a swapped statement in an earlier scan: the delta interval gives
`e^{r T}` and the exponential interval gives `1 + r T`.

## References

* J. Wallinga, M. Lipsitch, *How generation intervals shape the relationship between growth
  rates and reproductive numbers*, Proc. R. Soc. B 274 (2007), 599–604.
* M. Shaked, J. G. Shanthikumar, *Stochastic Orders*, Springer (2007), §3.A (convex order).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace MathlibExt.Biology.Epidemiology.EulerLotka

/-- The **reproductive number** implied by growth rate `r` and generation-interval law `g`:
`R = 1 / M_g(-r)` (Wallinga–Lipsitch 2007, eq. 2.9). -/
noncomputable def reproductionNumber (g : Measure ℝ) (r : ℝ) : ℝ :=
  (mgf id g (-r))⁻¹

/-- **Convex order**: `g₁ ≤cx g₂` if `∫ φ dg₁ ≤ ∫ φ dg₂` for every convex `φ : ℝ → ℝ` that is
integrable under both laws (Shaked–Shanthikumar 2007, §3.A). -/
def ConvexOrderLE (g₁ g₂ : Measure ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Integrable φ g₁ → Integrable φ g₂ →
    ∫ a, φ a ∂g₁ ≤ ∫ a, φ a ∂g₂

/-- **Renewal equation for exponential growth**: for `c ≠ 0`, the exponential
`b(t) = c e^{r t}` solves `b(t) = R ∫ b(t - a) g(da)` for every `t` iff `R M_g(-r) = 1`.
This is meaningful when `a ↦ e^{-r a}` is `g`-integrable; otherwise Lean's integral and
`M_g(-r)` are both `0` and both sides of the equivalence are false. -/
theorem renewal_exp_iff (g : Measure ℝ) {r c : ℝ} (R : ℝ) (hc : c ≠ 0) :
    (∀ t, c * exp (r * t) = R * ∫ a, c * exp (r * (t - a)) ∂g) ↔ R * mgf id g (-r) = 1 := by
  have key : ∀ t, ∫ a, c * exp (r * (t - a)) ∂g = c * exp (r * t) * mgf id g (-r) := by
    intro t
    have : ∀ a, c * exp (r * (t - a)) = (c * exp (r * t)) * exp (-r * id a) := by
      intro a; rw [mul_assoc, ← exp_add]; congr 2; simp; ring
    simp_rw [this, integral_const_mul, mgf]
  simp_rw [key]
  have hpos : c * exp (r * 0) ≠ 0 := by simpa using hc
  constructor
  · intro h
    have h0 := h 0
    have : c * exp (r * 0) * 1 = c * exp (r * 0) * (R * mgf id g (-r)) := by
      linear_combination h0
    exact (mul_left_cancel₀ hpos this).symm
  · intro h t
    linear_combination (-(c * exp (r * t))) * h

/-- **Euler–Lotka**: under the hypotheses of `renewal_exp_iff`, exponential growth at rate
`r` solves the renewal equation iff `R = 1 / M_g(-r)`. -/
theorem renewal_exp_iff_reproductionNumber (g : Measure ℝ) [IsProbabilityMeasure g]
    {r c : ℝ} (R : ℝ) (hc : c ≠ 0) (hint : Integrable (fun a => exp (-r * a)) g) :
    (∀ t, c * exp (r * t) = R * ∫ a, c * exp (r * (t - a)) ∂g) ↔
      R = reproductionNumber g r := by
  have hM : 0 < mgf id g (-r) := mgf_pos (X := id) hint
  rw [renewal_exp_iff g R hc, reproductionNumber]
  constructor
  · intro h; exact eq_inv_of_mul_eq_one_left h
  · intro h; rw [h, inv_mul_cancel₀ hM.ne']

/-- The reproductive number is positive when `M_g(-r)` is finite. -/
theorem reproductionNumber_pos (g : Measure ℝ) [IsProbabilityMeasure g] {r : ℝ}
    (hint : Integrable (fun a => exp (-r * a)) g) : 0 < reproductionNumber g r :=
  inv_pos.2 (mgf_pos (X := id) hint)

/-- **Fixed generation interval** `T`: `R = e^{r T}` (for all real `r`, `T`). -/
theorem reproductionNumber_dirac (r T : ℝ) : reproductionNumber (Measure.dirac T) r =
    exp (r * T) := by
  rw [reproductionNumber, mgf_dirac' (X := id)]
  simp [← exp_neg]

/-- **Gamma generation interval** with shape `α > 0` and rate `β > 0`: for `r > -β`,
`R = (1 + r / β)^α`. -/
theorem reproductionNumber_gammaMeasure {α β r : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hr : -β < r) : reproductionNumber (gammaMeasure α β) r = (1 + r / β) ^ α := by
  rw [reproductionNumber, mgf_gammaMeasure_of_lt hα hβ (by linarith)]
  have h1 : 0 < β / (β - -r) := div_pos hβ (by linarith)
  rw [← Real.inv_rpow h1.le, inv_div]
  congr 1
  field_simp
  ring

/-- **Exponential generation interval** with mean `T > 0` (rate `1 / T`): for `r T > -1`,
`R = 1 + r T` (Wallinga–Lipsitch 2007, eq. 3.1). -/
theorem reproductionNumber_expMeasure {r T : ℝ} (hT : 0 < T) (hr : -1 < r * T) :
    reproductionNumber (expMeasure T⁻¹) r = 1 + r * T := by
  have hr' : -T⁻¹ < r := by
    have : -1 / T < r := by rw [div_lt_iff₀ hT]; linarith
    simpa [neg_div, one_div] using this
  rw [expMeasure, reproductionNumber_gammaMeasure one_pos (inv_pos.2 hT) hr', Real.rpow_one,
    div_inv_eq_mul]

/-- **More spread lowers `R`**: if `g₁ ≤cx g₂` and both have finite `M(-r)`, then
`R(g₂) ≤ R(g₁)` at growth rate `r` (any real `r`). In particular, among generation intervals
with a given mean, the fixed interval maximizes `R`. -/
theorem reproductionNumber_le_of_convexOrderLE {g₁ g₂ : Measure ℝ} [IsProbabilityMeasure g₁]
    [IsProbabilityMeasure g₂] (h : ConvexOrderLE g₁ g₂) {r : ℝ}
    (h₁ : Integrable (fun a => exp (-r * a)) g₁) (h₂ : Integrable (fun a => exp (-r * a)) g₂) :
    reproductionNumber g₂ r ≤ reproductionNumber g₁ r := by
  have hc : ConvexOn ℝ Set.univ fun a : ℝ => exp (-r * a) :=
    convexOn_exp.comp_linearMap ((LinearMap.mul ℝ ℝ) (-r))
  have hle : mgf id g₁ (-r) ≤ mgf id g₂ (-r) := h _ hc h₁ h₂
  exact inv_anti₀ (mgf_pos (X := id) h₁) hle

/-- **Jensen bound**: if the generation interval has finite mean `T̄ = ∫ a g(da)` and finite
`M_g(-r)`, then `R ≤ e^{r T̄}` (any real `r`); Wallinga and Lipsitch (2007, §3) note that the
fixed interval gives this upper bound. -/
theorem reproductionNumber_le_exp_mean (g : Measure ℝ) [IsProbabilityMeasure g] {r : ℝ}
    (hid : Integrable id g) (hint : Integrable (fun a => exp (-r * a)) g) :
    reproductionNumber g r ≤ exp (r * ∫ a, a ∂g) := by
  have hc : ConvexOn ℝ Set.univ fun a : ℝ => exp (-r * a) :=
    convexOn_exp.comp_linearMap ((LinearMap.mul ℝ ℝ) (-r))
  have hJ : exp (-r * ∫ a, a ∂g) ≤ mgf id g (-r) :=
    hc.map_integral_le (by fun_prop) isClosed_univ (by simp) hid hint
  rw [reproductionNumber]
  refine inv_le_of_inv_le₀ (exp_pos _) ?_
  rw [← exp_neg, show -(r * ∫ a, a ∂g) = -r * ∫ a, a ∂g by ring]
  exact hJ

end MathlibExt.Biology.Epidemiology.EulerLotka
