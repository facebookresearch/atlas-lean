/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.ConstantInputRelaxation
public import Domains.Biology.Dynamics.FeedForwardLoop
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# One-compartment linear pharmacokinetics

The drug amount `A(t)` in a single well-mixed compartment of volume `V > 0` is eliminated with
clearance `CL ≥ 0` (volume per time) and infused at a constant rate `R ≥ 0` (amount per time).
With elimination rate constant `k = CL / V` (`elimRate`) the mass balance is

  `A' = R - k A`,   `A(0) = A₀`,

and the concentration is `C = A / V` (`concentration`). An intravenous bolus of dose `D` is the
initial amount `A₀ = D` with `R = 0`; the impulse itself is not modelled as an input function.

The amount (`amount`) is the constant-input case of the variation-of-constants solution
`FeedForwardLoop.relaxation` of `z' = P(t) - α z`, so the two developments share one solution
formula. Its explicit form is

  `A(t) = A∞ + (A₀ - A∞) e^{-k t}`, `A∞ = R / k`   for `k ≠ 0` (`amount_eq_of_ne_zero`),
  `A(t) = A₀ + R t`                                  for `k = 0` (`amount_rate_zero`).

## Main results

* `hasDerivAt_amount`, `isSolution_amount`, `amount_zero`: `A` solves the equation with
  `A(0) = A₀`; `IsSolution.eq_amount`: it is the only solution on `[0, ∞)`.
* `amount_nonneg`: nonnegative parameters and inputs give a nonnegative amount for `t ≥ 0`.
* `IsSolution.add_integral_eq`, `amount_add_eliminated`: mass balance
  `A(t) + ∫₀ᵗ k A = A₀ + R t` (for `k, R ≥ 0` and `A₀ ≥ 0`, amount present plus amount
  eliminated equals amount supplied).
* `integral_concentration_bolus`, `integral_Ici_concentration_bolus`: the bolus area under the
  concentration curve is `(D / CL)(1 - e^{-k T})` on `[0, T]` and `D / CL` on `[0, ∞)`.
* `tendsto_amount`, `tendsto_concentration`: under constant infusion `A → R / k` and
  `C → R / CL`; `amount_monotone`, `amount_antitone`, `amount_le_steadyAmount`,
  `steadyAmount_le_amount`: the approach is monotone, from the side of `A₀ - A∞`.
* `amount_bolus_add_halfLife`: a bolus halves every `t½ = log 2 / k`.
* `bolus_absolute_reconstruction`, `bolus_absolute_injective`: exact absolute bolus
  observations at `0` and at `t > 0` with known dose recover `V`, `CL / V` and `CL`.
* `normalized_washout_rate`, `normalized_scaling_same_washout`: the normalized washout
  `C(t) / C(0)` recovers `CL / V` without a known dose; scaling `(V, CL)` together
  leaves it unchanged while changing `V`.
* Boundaries: `amount_rate_zero_input_zero` (`k = 0`, `R = 0`: constant),
  `tendsto_amount_rate_zero_atTop`, `not_tendsto_amount_rate_zero`,
  `not_isSolution_const_rate_zero` (`k = 0`, `R > 0`: linear growth, no steady state),
  `amount_bolus`, `tendsto_amount_bolus` (`R = 0`: exponential washout).

This is a mathematical model only; it carries no dosing recommendation. Multi-compartment,
saturable (Michaelis–Menten) elimination and absorption models are not treated.

## References

* M. Gibaldi and D. Perrier, *Pharmacokinetics*, 2nd ed., Marcel Dekker (1982), ch. 1–2.
* M. Rowland and T. N. Tozer, *Clinical Pharmacokinetics and Pharmacodynamics*, 4th ed.,
  Lippincott Williams & Wilkins (2011), ch. 3 and 5.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics

/-- Elimination rate constant `k = CL / V` (per time) for clearance `CL` and volume `V`. With the
convention `x / 0 = 0` it is `0` when `V = 0`; in the model `V > 0` and `CL ≥ 0`. -/
noncomputable def elimRate (CL V : ℝ) : ℝ := CL / V

/-- Concentration `C(t) = A(t) / V` for clearance `CL`, volume `V`, infusion rate `R` and initial
amount `A₀`, with elimination rate `k = CL / V`. With the convention `x / 0 = 0` it is `0` when
`V = 0`; in the model `V > 0` and `CL ≥ 0`. -/
noncomputable def concentration (CL V R A₀ t : ℝ) : ℝ := amount (elimRate CL V) R A₀ t / V

variable {k R A₀ t : ℝ}

/-! ### The solution -/

theorem isSolution_amount (k R A₀ : ℝ) : IsSolution k R (amount k R A₀) :=
  fun t _ ↦ hasDerivAt_amount k R A₀ t

/-! ### Mass balance -/

/-- **Mass balance.** For all real `k`, `R` and any solution, `A(t) + ∫₀ᵗ k A = A(0) + R t` for
`t ≥ 0`. In the model, with `k ≥ 0`, `R ≥ 0` and `A(0) ≥ 0`, the amount present plus the amount
eliminated, `∫₀ᵗ k A(s) ds`, equals the initial amount plus the amount infused. -/
theorem IsSolution.add_integral_eq {A : ℝ → ℝ} (h : IsSolution k R A) (ht : 0 ≤ t) :
    A t + ∫ s in (0)..t, k * A s = A 0 + R * t := by
  have hd : ∀ s ∈ uIcc 0 t, HasDerivAt A (R - k * A s) s := fun s hs ↦
    h s (by rw [uIcc_of_le ht] at hs; exact hs.1)
  have hcont : ContinuousOn A (uIcc 0 t) := fun s hs ↦
    (hd s hs).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun s ↦ k * A s) volume 0 t :=
    (continuousOn_const.mul hcont).intervalIntegrable
  have hFTC := integral_eq_sub_of_hasDerivAt hd (intervalIntegrable_const.sub hint)
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
    intervalIntegral.integral_const] at hFTC
  simp only [sub_zero, smul_eq_mul] at hFTC
  linarith

/-- Mass balance for `amount`: `A(t) + ∫₀ᵗ k A = A₀ + R t` for `t ≥ 0`. -/
theorem amount_add_eliminated (ht : 0 ≤ t) :
    amount k R A₀ t + ∫ s in (0)..t, k * amount k R A₀ s = A₀ + R * t := by
  simpa using (isSolution_amount k R A₀).add_integral_eq ht

/-! ### Bolus: washout, area under the curve and half-life -/

/-- Bolus concentration `C(t) = (D / V) e^{-k t}`, `k = CL / V`, for all real inputs; with the
convention `x / 0 = 0` both sides are `0` when `V = 0`. -/
theorem concentration_bolus (CL V D t : ℝ) :
    concentration CL V 0 D t = D / V * exp (-elimRate CL V * t) := by
  rw [concentration, amount_bolus]
  ring

/-- **Finite-horizon AUC.** After a bolus dose `D`, `∫₀ᵀ C = (D / CL)(1 - e^{-k T})` with
`k = CL / V`, for `CL > 0` and `V > 0` (the model domain). -/
theorem integral_concentration_bolus {CL V : ℝ} (hCL : 0 < CL) (hV : 0 < V) (D T : ℝ) :
    ∫ t in (0)..T, concentration CL V 0 D t = D / CL * (1 - exp (-elimRate CL V * T)) := by
  have hk : elimRate CL V ≠ 0 := div_ne_zero hCL.ne' hV.ne'
  have h := integral_exp_neg_mul_sub hk T
  rw [intervalIntegral.integral_comp_sub_left (fun s ↦ exp (-elimRate CL V * s)) T] at h
  simp only [sub_self, sub_zero] at h
  simp_rw [concentration_bolus]
  rw [intervalIntegral.integral_const_mul, h, elimRate]
  field_simp

/-- The bolus concentration is integrable on `[0, ∞)` when `V > 0` and `CL > 0`. -/
theorem integrableOn_concentration_bolus {CL V : ℝ} (hCL : 0 < CL) (hV : 0 < V) (D : ℝ) :
    IntegrableOn (concentration CL V 0 D) (Ici 0) := by
  have hk : -elimRate CL V < 0 := neg_neg_of_pos (div_pos hCL hV)
  simp_rw [funext (concentration_bolus CL V D)]
  exact ((integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_mul_Ioi hk 0)).const_mul
    _

/-- **Bolus AUC** (Gibaldi–Perrier): the total area under the concentration curve after a bolus
dose `D` is `∫_{[0, ∞)} C = D / CL`, for `V > 0` and `CL > 0`. -/
theorem integral_Ici_concentration_bolus {CL V : ℝ} (hCL : 0 < CL) (hV : 0 < V) (D : ℝ) :
    ∫ t in Ici 0, concentration CL V 0 D t = D / CL := by
  have hk : -elimRate CL V < 0 := neg_neg_of_pos (div_pos hCL hV)
  simp_rw [concentration_bolus]
  rw [integral_Ici_eq_integral_Ioi, MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hk 0,
    elimRate]
  field_simp
  simp

/-- The finite-horizon AUC tends to the total AUC `D / CL` as `T → ∞`. -/
theorem tendsto_integral_concentration_bolus {CL V : ℝ} (hCL : 0 < CL) (hV : 0 < V) (D : ℝ) :
    Tendsto (fun T ↦ ∫ t in (0)..T, concentration CL V 0 D t) atTop (𝓝 (D / CL)) := by
  have he := tendsto_exp_neg_mul (k := elimRate CL V) (div_pos hCL hV)
  simp_rw [integral_concentration_bolus hCL hV]
  simpa using (he.const_sub 1).const_mul (D / CL)

/-- The half-life in terms of clearance and volume: `t½ = log 2 · V / CL`, for all real `CL` and
`V`; with the convention `x / 0 = 0` both sides are `0` when `CL = 0` or `V = 0`. -/
theorem halfLife_elimRate (CL V : ℝ) : halfLife (elimRate CL V) = log 2 * V / CL := by
  simp only [halfLife, elimRate]
  rw [div_div_eq_mul_div]

/-! ### Constant infusion: steady state -/

/-- Under constant infusion the concentration tends to `C∞ = R / CL`, for `V > 0` and
`CL > 0`. -/
theorem tendsto_concentration {CL V : ℝ} (hCL : 0 < CL) (hV : 0 < V) (R A₀ : ℝ) :
    Tendsto (concentration CL V R A₀) atTop (𝓝 (R / CL)) := by
  have h := (tendsto_amount (k := elimRate CL V) (div_pos hCL hV) R A₀).div_const V
  have he : steadyAmount (elimRate CL V) R / V = R / CL := by
    simp only [steadyAmount, elimRate]
    field_simp
  rw [he] at h
  exact h

/-- Starting at or below the steady state (`A₀ ≤ R / k`, `k > 0`), the amount is nondecreasing in
`t` (constant when `A₀ = R / k`). -/
theorem amount_monotone (hk : 0 < k) (h : A₀ ≤ steadyAmount k R) : Monotone (amount k R A₀) := by
  intro a b hab
  rw [amount_eq_of_ne_zero hk.ne', amount_eq_of_ne_zero hk.ne']
  have := mul_le_mul_of_nonpos_left (exp_le_exp.2 (by nlinarith : -k * b ≤ -k * a))
    (sub_nonpos.2 h)
  rw [steadyAmount] at this
  linarith


/-! ### Boundary cases -/

/-- `k = 0`, `R = 0`: the amount is constant. -/
theorem amount_rate_zero_input_zero (A₀ t : ℝ) : amount 0 0 A₀ t = A₀ := by
  simp [amount_rate_zero]

/-- `k = 0`, `R > 0`: the amount grows without bound. -/
theorem tendsto_amount_rate_zero_atTop (hR : 0 < R) (A₀ : ℝ) :
    Tendsto (amount 0 R A₀) atTop atTop := by
  simp_rw [funext (amount_rate_zero R A₀)]
  exact tendsto_atTop_add_const_left _ A₀ (tendsto_id.const_mul_atTop hR)

/-- `k = 0`, `R > 0`: the amount has no finite limit. -/
theorem not_tendsto_amount_rate_zero (hR : 0 < R) (A₀ L : ℝ) :
    ¬ Tendsto (amount 0 R A₀) atTop (𝓝 L) :=
  not_tendsto_nhds_of_tendsto_atTop (tendsto_amount_rate_zero_atTop hR A₀) L

/-- `k = 0`, `R ≠ 0`: there is no steady state, i.e. no constant solution. -/
theorem not_isSolution_const_rate_zero (hR : R ≠ 0) (a : ℝ) :
    ¬ IsSolution 0 R (fun _ ↦ a) := by
  intro h
  have := (h 0 le_rfl).unique (hasDerivAt_const 0 a)
  simp [hR] at this

/-- `k > 0`, `R = 0`: the amount washes out to `0`. -/
theorem tendsto_amount_bolus (hk : 0 < k) (A₀ : ℝ) :
    Tendsto (amount k 0 A₀) atTop (𝓝 0) := by
  simpa [steadyAmount] using tendsto_amount hk 0 A₀

/-! ### Absolute identification from exact bolus observations -/

set_option linter.unusedVariables false in
/-- **Absolute bolus reconstruction.** Exact noiseless bolus observations `C₀ = D / V` at time `0`
and `Ct = (D / V) * exp (-(CL / V) * t)` at time `t > 0`, with known dose `D > 0`, volume `V > 0`
and clearance `CL ≥ 0`, recover the volume, the elimination rate and the clearance. The two formulas
are `concentration_bolus` at times `0` and `t`. This is a statement about the model only; it is no
finite-sample estimator guarantee and no fit to an individual. The `CL ≥ 0` hypothesis states the
physical domain; the algebra itself needs less. -/
theorem bolus_absolute_reconstruction {D V CL t C0 Ct : ℝ}
    (hD : 0 < D) (hV : 0 < V) (hCL : 0 ≤ CL) (ht : 0 < t)
    (hC0 : C0 = D / V) (hCt : Ct = D / V * exp (-(CL / V) * t)) :
    0 < C0 ∧ 0 < Ct ∧ V = D / C0 ∧ CL / V = -Real.log (Ct / C0) / t ∧
      CL = -(V / t) * Real.log (Ct / C0) := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have hV' : V ≠ 0 := ne_of_gt hV
  have ht' : t ≠ 0 := ne_of_gt ht
  have hDV : 0 < D / V := div_pos hD hV
  have hDV' : D / V ≠ 0 := ne_of_gt hDV
  have hC0pos : 0 < C0 := by rw [hC0]; exact hDV
  have hCtpos : 0 < Ct := by rw [hCt]; exact mul_pos hDV (exp_pos _)
  have hVeq : V = D / C0 := by rw [hC0]; field_simp
  have hRatio : Ct / C0 = exp (-(CL / V) * t) := by
    rw [hCt, hC0]
    field_simp
  have hLog : Real.log (Ct / C0) = -(CL / V) * t := by
    rw [hRatio, Real.log_exp]
  have hRate : CL / V = -Real.log (Ct / C0) / t := by
    rw [hLog]; field_simp
  have hCLfinal : CL = -(V / t) * Real.log (Ct / C0) := by
    rw [hLog]; field_simp
  exact ⟨hC0pos, hCtpos, hVeq, hRate, hCLfinal⟩

set_option linter.unusedVariables false in
/-- The two exact absolute observations determine the pair `(V, CL)`: two
physical parameter pairs with the same known dose and sampling time giving
the same observations at `0` and at `t > 0` are equal. -/
theorem bolus_absolute_injective {D t V₁ V₂ CL₁ CL₂ : ℝ}
    (hD : 0 < D) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) (hCL₁ : 0 ≤ CL₁) (hCL₂ : 0 ≤ CL₂)
    (ht : 0 < t)
    (h0 : D / V₁ = D / V₂)
    (h1 : D / V₁ * exp (-(CL₁ / V₁) * t) = D / V₂ * exp (-(CL₂ / V₂) * t)) :
    V₁ = V₂ ∧ CL₁ = CL₂ := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have hV₁' : V₁ ≠ 0 := ne_of_gt hV₁
  have hV₂' : V₂ ≠ 0 := ne_of_gt hV₂
  have ht' : t ≠ 0 := ne_of_gt ht
  have hV : V₁ = V₂ := by
    have h := (div_eq_div_iff hV₁' hV₂').mp h0
    exact (mul_left_cancel₀ hD' h).symm
  subst hV
  have hDV₁ : D / V₁ ≠ 0 := ne_of_gt (div_pos hD hV₁)
  have hExp : exp (-(CL₁ / V₁) * t) = exp (-(CL₂ / V₁) * t) :=
    mul_left_cancel₀ hDV₁ h1
  have hArg : -(CL₁ / V₁) * t = -(CL₂ / V₁) * t :=
    Real.exp_strictMono.injective hExp
  have hNeg : -(CL₁ / V₁) = -(CL₂ / V₁) := mul_right_cancel₀ ht' hArg
  have hDiv : CL₁ / V₁ = CL₂ / V₁ := neg_inj.mp hNeg
  have hCL : CL₁ = CL₂ := by
    have hmul := congrArg (fun x => x * V₁) hDiv
    rwa [div_mul_cancel₀ CL₁ hV₁', div_mul_cancel₀ CL₂ hV₁'] at hmul
  exact ⟨rfl, hCL⟩

/-! ### Normalized identification from the washout ratio -/

set_option linter.unusedVariables false in
/-- **Normalized washout identifies the elimination rate.** For a
bolus concentration `C(t) = (D / V) * exp (-(CL / V) * t)` with
`D > 0`, `V > 0`, `CL ≥ 0`, the normalized washout `C(t) / C(0)` at
any `t > 0` recovers exactly the rate `CL / V`:
`-log (C(t) / C(0)) / t = CL / V`. The dose need not be known. -/
theorem normalized_washout_rate {D V CL t : ℝ}
    (hD : 0 < D) (hV : 0 < V) (hCL : 0 ≤ CL) (ht : 0 < t) :
    -Real.log (((D / V) * Real.exp (-(CL / V) * t)) / (D / V)) / t = CL / V :=
  (bolus_absolute_reconstruction hD hV hCL ht rfl rfl).2.2.2.1.symm

set_option linter.unusedVariables false in
/-- **Scaling obstruction for separate parameters.** Scaling `V` and
`CL` by the same `s > 0`, `s ≠ 1`, leaves the normalized washout
`exp (-(CL / V) * t)` unchanged at every time, while the volume
itself changes. Hence normalized observations do not identify the
volume `V`, nor the parameter pair `(V, CL)`, separately from the
ratio. Zero clearance is the exceptional boundary: at `CL = 0` the
scaling fixes `CL`, and the constant washout `1` forces `CL = 0`, so
no non-identifiability of `CL` alone is claimed there. -/
theorem normalized_scaling_same_washout {V CL s : ℝ}
    (hV : 0 < V) (hCL : 0 ≤ CL) (hs : 0 < s) (hs1 : s ≠ 1) :
    (∀ t : ℝ, Real.exp (-((s * CL) / (s * V)) * t) = Real.exp (-(CL / V) * t)) ∧
    s * V ≠ V := by
  have hV' : V ≠ 0 := ne_of_gt hV
  have hs' : s ≠ 0 := ne_of_gt hs
  have hratio : (s * CL) / (s * V) = CL / V := by
    field_simp
  constructor
  · intro t
    rw [hratio]
  · intro hcon
    apply hs1
    have h1 : s * V = 1 * V := by rw [one_mul]; exact hcon
    exact mul_right_cancel₀ hV' h1

end MathlibExt.Biology.Biophysics.CompartmentKinetics
