/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.FeedForwardLoop
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.MeanValue
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
  `A(t) + ∫₀ᵗ k A = A₀ + R t` (amount present plus amount eliminated equals amount supplied).
* `integral_concentration_bolus`, `integral_Ici_concentration_bolus`: the bolus area under the
  concentration curve is `(D / CL)(1 - e^{-k T})` on `[0, T]` and `D / CL` on `[0, ∞)`.
* `tendsto_amount`, `tendsto_concentration`: under constant infusion `A → R / k` and
  `C → R / CL`; `amount_monotone`, `amount_antitone`, `amount_le_steadyAmount`,
  `steadyAmount_le_amount`: the approach is monotone, from the side of `A₀ - A∞`.
* `amount_bolus_add_halfLife`: a bolus halves every `t½ = log 2 / k`.
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

open MathlibExt.Biology.Dynamics.FeedForwardLoop (relaxation hasDerivAt_relaxation)

/-- Elimination rate constant `k = CL / V` (per time) for clearance `CL` and volume `V`. -/
noncomputable def elimRate (CL V : ℝ) : ℝ := CL / V

/-- Amount in the compartment at time `t` for elimination rate `k`, constant infusion rate `R`
and initial amount `A₀`: the solution of `A' = R - k A`, `A(0) = A₀`, given by the
variation-of-constants formula `FeedForwardLoop.relaxation` with constant production `R`. -/
noncomputable def amount (k R A₀ t : ℝ) : ℝ := relaxation k (fun _ ↦ R) A₀ t

/-- Concentration `C(t) = A(t) / V` for clearance `CL`, volume `V`, infusion rate `R` and
initial amount `A₀`, with elimination rate `k = CL / V`. -/
noncomputable def concentration (CL V R A₀ t : ℝ) : ℝ := amount (elimRate CL V) R A₀ t / V

/-- Steady-state amount `A∞ = R / k` under constant infusion. Meaningful for `k > 0`. -/
noncomputable def steadyAmount (k R : ℝ) : ℝ := R / k

/-- Elimination half-life `t½ = log 2 / k`. Meaningful for `k > 0`. -/
noncomputable def halfLife (k : ℝ) : ℝ := log 2 / k

/-- `A` solves the one-compartment equation `A' = R - k A` at every time `t ≥ 0` (two-sided
derivative, as for the other ODE models in `MathlibExt.Biology`). -/
def IsSolution (k R : ℝ) (A : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt A (R - k * A t) t

variable {k R A₀ t : ℝ}

/-! ### The solution -/

@[simp]
theorem amount_zero (k R A₀ : ℝ) : amount k R A₀ 0 = A₀ := by
  simp [amount, relaxation]

theorem hasDerivAt_amount (k R A₀ t : ℝ) :
    HasDerivAt (amount k R A₀) (R - k * amount k R A₀ t) t :=
  hasDerivAt_relaxation A₀ (fun _ _ ↦ intervalIntegrable_const) continuousAt_const

theorem isSolution_amount (k R A₀ : ℝ) : IsSolution k R (amount k R A₀) :=
  fun t _ ↦ hasDerivAt_amount k R A₀ t

/-- `∫₀ᵗ e^{-k (t - s)} ds = (1 - e^{-k t}) / k` for `k ≠ 0`. -/
private theorem integral_exp_neg_mul_sub (hk : k ≠ 0) (t : ℝ) :
    ∫ s in (0)..t, exp (-k * (t - s)) = (1 - exp (-k * t)) / k := by
  have hd (s : ℝ) : HasDerivAt (fun s ↦ exp (-k * (t - s)) / k) (exp (-k * (t - s))) s := by
    have h := ((((hasDerivAt_id s).const_sub t).const_mul (-k)).exp).div_const k
    refine h.congr_deriv ?_
    rw [show (-k * -1 : ℝ) = k by ring, mul_div_assoc, div_self hk, mul_one]
    rfl
  rw [integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s)
    ((by fun_prop : Continuous fun s ↦ exp (-k * (t - s))).intervalIntegrable 0 t)]
  simp only [sub_self, mul_zero, exp_zero, sub_zero]
  ring

private theorem tendsto_exp_neg_mul (hk : 0 < k) :
    Tendsto (fun t ↦ exp (-k * t)) atTop (𝓝 0) :=
  (tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hk)).congr fun t ↦ by
    simp [neg_mul]

/-- **Explicit solution, `k ≠ 0`:** `A(t) = A∞ + (A₀ - A∞) e^{-k t}` with `A∞ = R / k`. -/
theorem amount_eq_of_ne_zero (hk : k ≠ 0) (R A₀ t : ℝ) :
    amount k R A₀ t = R / k + (A₀ - R / k) * exp (-k * t) := by
  simp only [amount, relaxation]
  rw [intervalIntegral.integral_mul_const, integral_exp_neg_mul_sub hk]
  ring

/-- **Explicit solution, `k = 0`:** without elimination the amount grows linearly,
`A(t) = A₀ + R t`. -/
theorem amount_rate_zero (R A₀ t : ℝ) : amount 0 R A₀ t = A₀ + R * t := by
  simp [amount, relaxation, mul_comm]

/-- **Uniqueness.** A solution of `A' = R - k A` on `[0, ∞)` is `amount k R (A 0)` there. -/
theorem IsSolution.eq_amount {A : ℝ → ℝ} (h : IsSolution k R A) (ht : 0 ≤ t) :
    A t = amount k R (A 0) t := by
  set D : ℝ → ℝ := fun s ↦ (A s - amount k R (A 0) s) * exp (k * s)
  have hD (s : ℝ) (hs : 0 ≤ s) : HasDerivAt D 0 s := by
    have h' : HasDerivAt D (((R - k * A s) - (R - k * amount k R (A 0) s)) * exp (k * s) +
        (A s - amount k R (A 0) s) * (exp (k * s) * (k * 1))) s :=
      ((h s hs).sub (hasDerivAt_amount k R (A 0) s)).mul (((hasDerivAt_id s).const_mul k).exp)
    convert h' using 1
    ring
  have hconst := constant_of_has_deriv_right_zero (f := D) (a := 0) (b := t)
    (fun s hs ↦ (hD s hs.1).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hD s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  simp only [D, amount_zero, sub_self, zero_mul, mul_eq_zero, exp_ne_zero, or_false] at hconst
  linarith

/-- **Nonnegativity.** For `k ≥ 0`, `R ≥ 0` and `A₀ ≥ 0` the amount stays nonnegative for
`t ≥ 0`. -/
theorem amount_nonneg (hk : 0 ≤ k) (hR : 0 ≤ R) (hA₀ : 0 ≤ A₀) (ht : 0 ≤ t) :
    0 ≤ amount k R A₀ t := by
  rcases hk.eq_or_lt with rfl | hk
  · rw [amount_rate_zero]
    positivity
  · rw [amount_eq_of_ne_zero hk.ne']
    have he : exp (-k * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
    have hRk : 0 ≤ R / k := div_nonneg hR hk.le
    nlinarith [exp_pos (-k * t)]

/-! ### Mass balance -/

/-- **Mass balance.** For any solution, the amount present plus the amount eliminated,
`∫₀ᵗ k A(s) ds`, equals the initial amount plus the amount infused: `A(t) + ∫₀ᵗ k A = A₀ + R t`
for `t ≥ 0`. -/
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

/-- **Exponential washout.** After a bolus (`R = 0`) the amount is `A₀ e^{-k t}`, for every
`k` (including `k = 0`, where it is constant). -/
theorem amount_bolus (k A₀ t : ℝ) : amount k 0 A₀ t = A₀ * exp (-k * t) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [amount_rate_zero]
  · simp [amount_eq_of_ne_zero hk]

/-- Bolus concentration `C(t) = (D / V) e^{-k t}`, `k = CL / V`. -/
theorem concentration_bolus (CL V D t : ℝ) :
    concentration CL V 0 D t = D / V * exp (-elimRate CL V * t) := by
  rw [concentration, amount_bolus]
  ring

/-- **Finite-horizon AUC.** After a bolus dose `D`, `∫₀ᵀ C = (D / CL)(1 - e^{-k T})` with
`k = CL / V`, for `V ≠ 0` and `CL ≠ 0`. -/
theorem integral_concentration_bolus {CL V : ℝ} (hCL : CL ≠ 0) (hV : V ≠ 0) (D T : ℝ) :
    ∫ t in (0)..T, concentration CL V 0 D t = D / CL * (1 - exp (-elimRate CL V * T)) := by
  have hk : elimRate CL V ≠ 0 := div_ne_zero hCL hV
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
  simp_rw [integral_concentration_bolus hCL.ne' hV.ne']
  simpa using (he.const_sub 1).const_mul (D / CL)

/-- The half-life in terms of clearance and volume: `t½ = log 2 · V / CL`. -/
theorem halfLife_elimRate (CL V : ℝ) : halfLife (elimRate CL V) = log 2 * V / CL := by
  simp only [halfLife, elimRate]
  rw [div_div_eq_mul_div]

/-- **Half-life.** After a bolus the amount halves over every interval of length
`t½ = log 2 / k`, for `k ≠ 0`. -/
theorem amount_bolus_add_halfLife (hk : k ≠ 0) (A₀ t : ℝ) :
    amount k 0 A₀ (t + halfLife k) = amount k 0 A₀ t / 2 := by
  rw [amount_bolus, amount_bolus, halfLife,
    show -k * (t + log 2 / k) = -k * t - log 2 by field_simp; ring, exp_sub, exp_log two_pos]
  ring

/-! ### Constant infusion: steady state -/

/-- Under constant infusion with `k > 0` the amount tends to `A∞ = R / k`. -/
theorem tendsto_amount (hk : 0 < k) (R A₀ : ℝ) :
    Tendsto (amount k R A₀) atTop (𝓝 (steadyAmount k R)) := by
  have he := tendsto_exp_neg_mul hk
  simp_rw [funext (amount_eq_of_ne_zero hk.ne' R A₀), steadyAmount]
  simpa using (he.const_mul (A₀ - R / k)).const_add (R / k)

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

/-- Starting below the steady state (`A₀ ≤ R / k`, `k > 0`), the amount increases. -/
theorem amount_monotone (hk : 0 < k) (h : A₀ ≤ steadyAmount k R) : Monotone (amount k R A₀) := by
  intro a b hab
  rw [amount_eq_of_ne_zero hk.ne', amount_eq_of_ne_zero hk.ne']
  have := mul_le_mul_of_nonpos_left (exp_le_exp.2 (by nlinarith : -k * b ≤ -k * a))
    (sub_nonpos.2 h)
  rw [steadyAmount] at this
  linarith

/-- Starting above the steady state (`R / k ≤ A₀`, `k > 0`), the amount decreases. -/
theorem amount_antitone (hk : 0 < k) (h : steadyAmount k R ≤ A₀) : Antitone (amount k R A₀) := by
  intro a b hab
  rw [amount_eq_of_ne_zero hk.ne', amount_eq_of_ne_zero hk.ne']
  have := mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith : -k * b ≤ -k * a))
    (sub_nonneg.2 h)
  rw [steadyAmount] at this
  linarith

/-- Starting below the steady state, the amount never exceeds it. -/
theorem amount_le_steadyAmount (hk : 0 < k) (h : A₀ ≤ steadyAmount k R) (t : ℝ) :
    amount k R A₀ t ≤ steadyAmount k R := by
  rw [amount_eq_of_ne_zero hk.ne']
  rw [steadyAmount] at *
  nlinarith [exp_pos (-k * t)]

/-- Starting above the steady state, the amount never falls below it. -/
theorem steadyAmount_le_amount (hk : 0 < k) (h : steadyAmount k R ≤ A₀) (t : ℝ) :
    steadyAmount k R ≤ amount k R A₀ t := by
  rw [amount_eq_of_ne_zero hk.ne']
  rw [steadyAmount] at *
  nlinarith [exp_pos (-k * t)]

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

end MathlibExt.Biology.Biophysics.CompartmentKinetics
