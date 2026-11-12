/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Biophysics.CompartmentKinetics
public import MathlibExt.Biology.Dynamics.MichaelisMenten
import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# One-compartment pharmacokinetics with saturable (Michaelis–Menten) elimination

The plasma concentration `C(t)` in a single well-mixed compartment is eliminated by a saturable
process with maximal rate `Vmax > 0` (concentration per time) and Michaelis constant `Km > 0`
(concentration), and infused at a constant rate `R ≥ 0` (concentration per time, i.e. the amount
infusion rate divided by the volume):

  `C' = R - Vmax C / (Km + C)`,   `C(0) = C₀ ≥ 0`.

The elimination rate is the Michaelis–Menten rate law
`MathlibExt.Biology.Dynamics.MichaelisMenten.mmRate Vmax Km C`. An intravenous bolus of dose `D`
into volume `V` is the initial value `C₀ = D / V` with `R = 0`. `IsSolution Vmax Km R C` asks for
the equation at every `t ≥ 0`, with a two-sided derivative (as in
`MathlibExt.Biology.Biophysics.CompartmentKinetics`).

For small concentrations `mmRate Vmax Km C ≈ (Vmax / Km) C`, so the linear model of
`CompartmentKinetics` with elimination rate `k = Vmax / Km` is the low-concentration limit. For
large concentrations elimination saturates at the zero-order rate `Vmax`.

## Main results

* `exists_isSolution`, `IsSolution.eq_of_initial`: for `C₀ ≥ 0`, `R ≥ 0` a solution on `[0, ∞)`
  exists, and two solutions with the same initial value agree on `[0, ∞)`. The existence proof
  applies the global Picard–Lindelöf theorem
  `MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz` to the
  field clamped at `C = 0`, then shows the solution never needs the clamp.
* `IsSolution.nonneg`, `IsSolution.pos`: every solution with `C₀ ≥ 0` (resp. `C₀ > 0`) stays
  nonnegative (resp. positive).
* `IsSolution.amount_le`: the first-order washout `C₀ e^{-(Vmax/Km) t}`
  (`CompartmentKinetics.amount (Vmax / Km) 0 C₀ t`) is a lower barrier for every solution with
  `R ≥ 0`. `IsSolution.add_mul_le`, `IsSolution.le_add_mul`: the zero-order bounds
  `C₀ + (R - Vmax) t ≤ C(t) ≤ C₀ + R t`.
* `IsSolution.add_integral_eq`: mass balance `C(t) + ∫₀ᵗ mmRate(C) = C₀ + R t`.
* Bolus (`R = 0`): `IsSolution.antitoneOn_bolus` (monotone washout),
  `IsSolution.le_amount_bolus` (upper barrier `C₀ e^{-(Vmax/(Km + C₀)) t}`),
  `IsSolution.tendsto_bolus` (`C → 0`).
* Bolus AUC: `IsSolution.integral_bolus` (integrated balance on `[0, T]`),
  `IsSolution.integrableOn_Ioi_bolus` (the AUC is finite) and
  `IsSolution.integral_Ioi_bolus`: `∫₀^∞ C = C₀ (Km + C₀ / 2) / Vmax` (`bolusAUC`).
* Dose–AUC nonlinearity: `bolusAUC_eq_integral_linear_add` (AUC = linear AUC with clearance
  `V Vmax / Km`, plus `C₀² / (2 Vmax)`), `two_mul_bolusAUC_lt` (doubling the dose more than
  doubles the AUC), `strictMonoOn_bolusAUC_div` (dose-normalized AUC increases),
  `not_exists_bolusAUC_eq_mul` (AUC is not proportional to dose, unlike linear elimination),
  `tendsto_bolusAUC_div` (low-dose limit `Km / Vmax`).
* Constant infusion: `isSolution_const_iff`, `mmRate_steadyConc`, `eq_steadyConc_of_mmRate_eq`:
  for `R < Vmax` the unique nonnegative steady state is `C∞ = R Km / (Vmax - R)` (`steadyConc`).
  `IsSolution.abs_sub_steadyConc_le`, `IsSolution.tendsto_steadyConc`: every solution converges
  to it exponentially. `not_isSolution_const_of_le`, `IsSolution.tendsto_atTop`: for `R ≥ Vmax`
  there is no nonnegative steady state, and for `R > Vmax` the concentration grows without
  bound (infusion faster than the elimination capacity).

This is a mathematical model only; it carries no dosing recommendation. Closed forms via the
Lambert `W` function, the boundary case `R = Vmax` beyond the absence of a steady state, and
multi-compartment or absorption models are not treated.

## References

* M. Gibaldi and D. Perrier, *Pharmacokinetics*, 2nd ed., Marcel Dekker (1982), ch. 7.
* M. Rowland and T. N. Tozer, *Clinical Pharmacokinetics and Pharmacodynamics*, 4th ed.,
  Lippincott Williams & Wilkins (2011), ch. 20.
* J. G. Wagner, *Properties of the Michaelis–Menten equation and its integrated form which are
  useful in pharmacokinetics*, J. Pharmacokin. Biopharm. 1 (1973) 103–121.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace MathlibExt.Biology.Biophysics.SaturableElimination

open MathlibExt.Biology.Dynamics.MichaelisMenten (mmRate mmRate_lt)
open MathlibExt.Biology.Biophysics.CompartmentKinetics (amount concentration amount_bolus
  integral_Ici_concentration_bolus tendsto_amount_bolus)

/-- `C` solves the saturable-elimination equation `C' = R - Vmax C / (Km + C)` at every time
`t ≥ 0` (two-sided derivative), with elimination rate `mmRate Vmax Km C` and constant infusion
rate `R`. -/
def IsSolution (Vmax Km R : ℝ) (C : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt C (R - mmRate Vmax Km (C t)) t

/-- Steady-state concentration `C∞ = R Km / (Vmax - R)` under constant infusion `R`. Meaningful
for `0 ≤ R < Vmax`, where it is the unique nonnegative root of `mmRate Vmax Km C = R`. -/
noncomputable def steadyConc (Vmax Km R : ℝ) : ℝ := R * Km / (Vmax - R)

/-- Area under the concentration curve after a bolus giving initial concentration `C₀`:
`AUC = C₀ (Km + C₀ / 2) / Vmax`. -/
noncomputable def bolusAUC (Vmax Km C₀ : ℝ) : ℝ := C₀ * (Km + C₀ / 2) / Vmax

variable {Vmax Km R t : ℝ} {C : ℝ → ℝ}

/-! ### The elimination rate -/

/-- Elimination is nonnegative at nonnegative concentrations. -/
theorem mmRate_nonneg (hV : 0 ≤ Vmax) (hK : 0 < Km) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ mmRate Vmax Km c := by
  unfold mmRate; positivity

/-- Zero-order bound: elimination never exceeds `Vmax`. -/
theorem mmRate_le (hV : 0 ≤ Vmax) (hK : 0 < Km) {c : ℝ} (hc : 0 ≤ c) :
    mmRate Vmax Km c ≤ Vmax := by
  unfold mmRate
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- First-order bound: elimination is at most the linear rate `(Vmax / Km) c`. -/
theorem mmRate_le_mul (hV : 0 ≤ Vmax) (hK : 0 < Km) {c : ℝ} (hc : 0 ≤ c) :
    mmRate Vmax Km c ≤ Vmax / Km * c := by
  unfold mmRate
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hK (by linarith)

/-- On `0 ≤ c ≤ M` elimination is at least the linear rate `(Vmax / (Km + M)) c`. -/
theorem mul_le_mmRate (hV : 0 ≤ Vmax) (hK : 0 < Km) {c M : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M) :
    Vmax / (Km + M) * c ≤ mmRate Vmax Km c := by
  unfold mmRate
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- The field in deviation form: `R - mmRate Vmax Km c = -(Vmax - R) (c - C∞) / (Km + c)`. -/
theorem sub_mmRate_eq {c : ℝ} (hc : Km + c ≠ 0) (hRV : Vmax - R ≠ 0) :
    R - mmRate Vmax Km c = -(Vmax - R) * (c - steadyConc Vmax Km R) / (Km + c) := by
  unfold mmRate steadyConc
  field_simp
  ring

private theorem abs_mmRate_sub_le (hV : 0 ≤ Vmax) (hK : 0 < Km) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : |mmRate Vmax Km a - mmRate Vmax Km b| ≤ Vmax / Km * |a - b| := by
  have e : mmRate Vmax Km a - mmRate Vmax Km b =
      Vmax * Km * (a - b) / ((Km + a) * (Km + b)) := by
    unfold mmRate
    field_simp
    ring
  rw [e, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Vmax * Km),
    abs_of_pos (by positivity : 0 < (Km + a) * (Km + b)), div_le_iff₀ (by positivity)]
  have h1 : Km * Km ≤ (Km + a) * (Km + b) := by nlinarith
  calc Vmax * Km * |a - b| = Vmax / Km * |a - b| * (Km * Km) := by
        field_simp
    _ ≤ Vmax / Km * |a - b| * ((Km + a) * (Km + b)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The field clamped at `c = 0`; it agrees with the true field on `c ≥ 0` and is globally
Lipschitz. -/
private noncomputable def clamp (Vmax Km R c : ℝ) : ℝ := R - mmRate Vmax Km (max c 0)

private theorem lipschitzWith_clamp (hV : 0 ≤ Vmax) (hK : 0 < Km) :
    LipschitzWith (Real.toNNReal (Vmax / Km)) (clamp Vmax Km R) := by
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity), clamp, clamp,
    show R - mmRate Vmax Km (max a 0) - (R - mmRate Vmax Km (max b 0)) =
      -(mmRate Vmax Km (max a 0) - mmRate Vmax Km (max b 0)) by ring, abs_neg]
  exact (abs_mmRate_sub_le hV hK (le_max_right a 0) (le_max_right b 0)).trans
    (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs a b 0) (by positivity))

/-! ### Comparison helpers -/

/-- A function whose derivative is nonnegative on `[0, ∞)` is monotone there. -/
private theorem le_of_hasDerivAt_nonneg {g g' : ℝ → ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t) (hg' : ∀ t, 0 ≤ t → 0 ≤ g' t) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : g s ≤ g t :=
  image_le_of_deriv_right_le_deriv_boundary (f := fun _ ↦ g s) (f' := fun _ ↦ 0) (a := s)
    (b := t) continuousOn_const (fun _ _ ↦ (hasDerivAt_const _ _).hasDerivWithinAt) le_rfl
    (fun r hr ↦ (hd r (hs.trans hr.1)).continuousAt.continuousWithinAt)
    (fun r hr ↦ (hd r (hs.trans hr.1)).hasDerivWithinAt) (fun r hr ↦ hg' r (hs.trans hr.1))
    ⟨hst, le_rfl⟩

/-- Barrier at `0`: if `x(0) ≥ 0` and `x' ≥ 0` whenever `-δ < x < 0`, then `x ≥ 0` on
`[0, ∞)`. -/
private theorem nonneg_of_barrier {x x' : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt x (x' t) t) (h0 : 0 ≤ x 0)
    (hbd : ∀ t, 0 ≤ t → -δ < x t → x t < 0 → 0 ≤ x' t) {T : ℝ} (hT : 0 ≤ T) : 0 ≤ x T := by
  by_contra hneg
  push Not at hneg
  set m := min δ (-x T) with hm
  have hmpos : 0 < m := lt_min hδ (by linarith)
  have h1T : 0 < 1 + T := by linarith
  set ε := m / (2 * (1 + T)) with hε
  have hεpos : 0 < ε := by positivity
  have hεT : ε * (1 + T) = m / 2 := by
    rw [hε]
    field_simp
  have hcmp := image_le_of_deriv_right_lt_deriv_boundary' (f := fun t ↦ -x t)
    (f' := fun t ↦ -x' t) (a := 0) (b := T) (B := fun t ↦ ε * (1 + t)) (B' := fun _ ↦ ε)
    (fun t ht ↦ (hd t ht.1).continuousAt.continuousWithinAt.neg)
    (fun t ht ↦ (hd t ht.1).neg.hasDerivWithinAt)
    (by simp only [add_zero, mul_one]; linarith)
    (by fun_prop)
    (fun t _ ↦ ((((hasDerivAt_id' t).const_add 1).const_mul ε).congr_deriv
      (mul_one ε)).hasDerivWithinAt)
    (fun t ht heq ↦ by
      have h1 : ε * (1 + t) ≤ ε * (1 + T) := by nlinarith [ht.2]
      have h2 : m ≤ δ := min_le_left _ _
      have h3 : 0 < ε * (1 + t) := mul_pos hεpos (by linarith [ht.1])
      have := hbd t ht.1 (by nlinarith) (by linarith)
      linarith)
    ⟨hT, le_rfl⟩
  have : m ≤ -x T := min_le_right _ _
  nlinarith

/-! ### Existence, uniqueness, positivity -/

/-- **Nonnegativity.** For `Vmax ≥ 0`, `Km > 0`, `R ≥ 0`, every solution with `C(0) ≥ 0` stays
nonnegative on `[0, ∞)`. -/
theorem IsSolution.nonneg (h : IsSolution Vmax Km R C) (hV : 0 ≤ Vmax) (hK : 0 < Km)
    (hR : 0 ≤ R) (h0 : 0 ≤ C 0) (ht : 0 ≤ t) : 0 ≤ C t :=
  nonneg_of_barrier (x' := fun s ↦ R - mmRate Vmax Km (C s)) hK h h0 (fun s _ h1 h2 ↦ by
    have : mmRate Vmax Km (C s) ≤ 0 := by
      unfold mmRate
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hV h2.le)
        (by linarith)
    linarith) ht

/-- **Existence.** For `Vmax ≥ 0`, `Km > 0`, `R ≥ 0` and `C₀ ≥ 0` there is a solution on
`[0, ∞)` with `C(0) = C₀`; it is nonnegative. -/
theorem exists_isSolution (hV : 0 ≤ Vmax) (hK : 0 < Km) (hR : 0 ≤ R) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ → ℝ, IsSolution Vmax Km R C ∧ C 0 = C₀ ∧ ∀ t, 0 ≤ t → 0 ≤ C t := by
  have hlip := lipschitzWith_clamp (R := R) hV hK
  obtain ⟨x, ⟨hx0, hx⟩, -⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
      (fun _ ↦ clamp Vmax Km R) 0 C₀ _ (hlip.continuous.comp continuous_snd) (fun _ ↦ hlip)
  have hnn : ∀ t, 0 ≤ t → 0 ≤ x t := fun t ht ↦
    nonneg_of_barrier one_pos (x' := fun t ↦ clamp Vmax Km R (x t)) (fun t _ ↦ hx t)
      (hx0 ▸ hC₀) (fun s _ _ h2 ↦ by simp [clamp, max_eq_right h2.le, mmRate, hR]) ht
  refine ⟨x, fun t ht ↦ ?_, hx0, hnn⟩
  have := hx t
  rwa [clamp, max_eq_left (hnn t ht)] at this

/-- **Uniqueness.** For `Vmax ≥ 0`, `Km > 0`, `R ≥ 0`, two solutions with the same initial value
`C(0) ≥ 0` agree on `[0, ∞)`. -/
theorem IsSolution.eq_of_initial {D : ℝ → ℝ} (h₁ : IsSolution Vmax Km R C)
    (h₂ : IsSolution Vmax Km R D) (hV : 0 ≤ Vmax) (hK : 0 < Km) (hR : 0 ≤ R) (h0 : 0 ≤ C 0)
    (hCD : C 0 = D 0) (ht : 0 ≤ t) : C t = D t := by
  have key : ∀ {E : ℝ → ℝ}, IsSolution Vmax Km R E → 0 ≤ E 0 → ∀ s, 0 ≤ s →
      HasDerivAt E (clamp Vmax Km R (E s)) s := by
    intro E hE hE0 s hs
    rw [clamp, max_eq_left (hE.nonneg hV hK hR hE0 hs)]
    exact hE s hs
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ clamp Vmax Km R)
    (s := fun _ ↦ univ) (K := Real.toNNReal (Vmax / Km))
    (fun _ _ ↦ (lipschitzWith_clamp hV hK).lipschitzOnWith)
    (fun s hs ↦ (h₁ s hs.1).continuousAt.continuousWithinAt)
    (fun s hs ↦ (key h₁ h0 s hs.1).hasDerivWithinAt) (fun _ _ ↦ mem_univ _)
    (fun s hs ↦ (h₂ s hs.1).continuousAt.continuousWithinAt)
    (fun s hs ↦ (key h₂ (hCD ▸ h0) s hs.1).hasDerivWithinAt) (fun _ _ ↦ mem_univ _) hCD
    ⟨ht, le_rfl⟩

/-! ### Bounds and mass balance -/

/-- **Linear lower barrier.** For `Vmax ≥ 0`, `Km > 0`, `R ≥ 0` and `C(0) ≥ 0`, a solution is
at least the first-order washout with rate `Vmax / Km` (the linear model of `CompartmentKinetics`
with no infusion): `C₀ e^{-(Vmax / Km) t} ≤ C(t)`. -/
theorem IsSolution.amount_le (h : IsSolution Vmax Km R C) (hV : 0 ≤ Vmax) (hK : 0 < Km)
    (hR : 0 ≤ R) (h0 : 0 ≤ C 0) (ht : 0 ≤ t) : amount (Vmax / Km) 0 (C 0) t ≤ C t := by
  rw [amount_bolus]
  set k := Vmax / Km
  have hmono := le_of_hasDerivAt_nonneg (g := fun s ↦ C s * exp (k * s))
    (g' := fun s ↦ (R - mmRate Vmax Km (C s) + k * C s) * exp (k * s))
    (fun s hs ↦ ((h s hs).mul ((hasDerivAt_id' s).const_mul k).exp).congr_deriv (by ring))
    (fun s hs ↦ by
      have := mmRate_le_mul hV hK (h.nonneg hV hK hR h0 hs)
      exact mul_nonneg (by linarith) (exp_pos _).le)
    le_rfl ht
  simp only [mul_zero, exp_zero, mul_one] at hmono
  calc C 0 * exp (-k * t) ≤ C t * exp (k * t) * exp (-k * t) :=
        mul_le_mul_of_nonneg_right hmono (exp_pos _).le
    _ = C t := by rw [mul_assoc, ← exp_add]; simp

/-- **Positivity.** For `Vmax ≥ 0`, `Km > 0`, `R ≥ 0`, a solution with `C(0) > 0` stays
positive on `[0, ∞)`. -/
theorem IsSolution.pos (h : IsSolution Vmax Km R C) (hV : 0 ≤ Vmax) (hK : 0 < Km) (hR : 0 ≤ R)
    (h0 : 0 < C 0) (ht : 0 ≤ t) : 0 < C t := by
  have := h.amount_le hV hK hR h0.le ht
  rw [amount_bolus] at this
  exact lt_of_lt_of_le (by positivity) this

/-- **Input bound.** A nonnegative solution never exceeds the elimination-free accumulation:
`C(t) ≤ C₀ + R t`. -/
theorem IsSolution.le_add_mul (h : IsSolution Vmax Km R C) (hV : 0 ≤ Vmax) (hK : 0 < Km)
    (hR : 0 ≤ R) (h0 : 0 ≤ C 0) (ht : 0 ≤ t) : C t ≤ C 0 + R * t := by
  have := le_of_hasDerivAt_nonneg (g := fun s ↦ C 0 + R * s - C s)
    (g' := fun s ↦ mmRate Vmax Km (C s))
    (fun s hs ↦ ((((hasDerivAt_id' s).const_mul R).const_add (C 0)).sub (h s hs)).congr_deriv
      (by ring))
    (fun s hs ↦ mmRate_nonneg hV hK (h.nonneg hV hK hR h0 hs)) le_rfl ht
  simp only [mul_zero, add_zero, sub_self] at this
  linarith

/-- **Zero-order bound.** Elimination is at most `Vmax`, so `C₀ + (R - Vmax) t ≤ C(t)`. -/
theorem IsSolution.add_mul_le (h : IsSolution Vmax Km R C) (hV : 0 ≤ Vmax) (hK : 0 < Km)
    (hR : 0 ≤ R) (h0 : 0 ≤ C 0) (ht : 0 ≤ t) : C 0 + (R - Vmax) * t ≤ C t := by
  have := le_of_hasDerivAt_nonneg (g := fun s ↦ C s - (R - Vmax) * s)
    (g' := fun s ↦ Vmax - mmRate Vmax Km (C s))
    (fun s hs ↦ ((h s hs).sub ((hasDerivAt_id' s).const_mul (R - Vmax))).congr_deriv (by ring))
    (fun s hs ↦ sub_nonneg.2 (mmRate_le hV hK (h.nonneg hV hK hR h0 hs))) le_rfl ht
  simp only [mul_zero, sub_zero] at this
  linarith

private theorem IsSolution.continuousOn_mmRate (h : IsSolution Vmax Km R C) (hV : 0 ≤ Vmax)
    (hK : 0 < Km) (hR : 0 ≤ R) (h0 : 0 ≤ C 0) (ht : 0 ≤ t) :
    ContinuousOn (fun s ↦ mmRate Vmax Km (C s)) (uIcc 0 t) := by
  have hcont : ContinuousOn C (uIcc 0 t) := fun s hs ↦
    (h s (by rw [uIcc_of_le ht] at hs; exact hs.1)).continuousAt.continuousWithinAt
  unfold mmRate
  refine (continuousOn_const.mul hcont).div (continuousOn_const.add hcont) fun s hs ↦ ?_
  have := h.nonneg hV hK hR h0 (t := s) (by rw [uIcc_of_le ht] at hs; exact hs.1)
  exact ne_of_gt (by linarith)

/-- **Mass balance.** The concentration present plus the concentration eliminated equals the
initial concentration plus the concentration infused: `C(t) + ∫₀ᵗ mmRate(C) = C₀ + R t`. -/
theorem IsSolution.add_integral_eq (h : IsSolution Vmax Km R C) (hV : 0 ≤ Vmax) (hK : 0 < Km)
    (hR : 0 ≤ R) (h0 : 0 ≤ C 0) (ht : 0 ≤ t) :
    C t + ∫ s in (0)..t, mmRate Vmax Km (C s) = C 0 + R * t := by
  have hd : ∀ s ∈ uIcc 0 t, HasDerivAt C (R - mmRate Vmax Km (C s)) s := fun s hs ↦
    h s (by rw [uIcc_of_le ht] at hs; exact hs.1)
  have hint : IntervalIntegrable (fun s ↦ mmRate Vmax Km (C s)) volume 0 t :=
    (h.continuousOn_mmRate hV hK hR h0 ht).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (intervalIntegrable_const.sub hint)
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
    intervalIntegral.integral_const] at hFTC
  simp only [sub_zero, smul_eq_mul] at hFTC
  linarith

/-! ### Bolus: washout -/

/-- After a bolus (`R = 0`) the concentration decreases. -/
theorem IsSolution.antitoneOn_bolus (h : IsSolution Vmax Km 0 C) (hV : 0 ≤ Vmax) (hK : 0 < Km)
    (h0 : 0 ≤ C 0) : AntitoneOn C (Ici 0) := by
  intro s hs r _ hsr
  have := le_of_hasDerivAt_nonneg (g := fun r ↦ -C r) (g' := fun r ↦ mmRate Vmax Km (C r))
    (fun r hr ↦ (h r hr).neg.congr_deriv (by ring))
    (fun r hr ↦ mmRate_nonneg hV hK (h.nonneg hV hK le_rfl h0 hr)) hs hsr
  linarith

/-- **Upper barrier after a bolus.** Since `C ≤ C₀`, elimination is at least first order with
the slowest rate `Vmax / (Km + C₀)`: `C(t) ≤ C₀ e^{-(Vmax / (Km + C₀)) t}`. Together with
`IsSolution.amount_le` this brackets the bolus curve between two linear washouts. -/
theorem IsSolution.le_amount_bolus (h : IsSolution Vmax Km 0 C) (hV : 0 ≤ Vmax) (hK : 0 < Km)
    (h0 : 0 ≤ C 0) (ht : 0 ≤ t) : C t ≤ amount (Vmax / (Km + C 0)) 0 (C 0) t := by
  rw [amount_bolus]
  set μ := Vmax / (Km + C 0)
  have hmono := le_of_hasDerivAt_nonneg (g := fun s ↦ -(C s * exp (μ * s)))
    (g' := fun s ↦ (mmRate Vmax Km (C s) - μ * C s) * exp (μ * s))
    (fun s hs ↦ ((h s hs).mul ((hasDerivAt_id' s).const_mul μ).exp).neg.congr_deriv (by ring))
    (fun s hs ↦ mul_nonneg (sub_nonneg.2 (mul_le_mmRate hV hK (h.nonneg hV hK le_rfl h0 hs)
      (h.antitoneOn_bolus hV hK h0 (mem_Ici.2 le_rfl) (mem_Ici.2 hs) hs))) (exp_pos _).le)
    le_rfl ht
  simp only [mul_zero, exp_zero, mul_one] at hmono
  calc C t = C t * exp (μ * t) * exp (-μ * t) := by rw [mul_assoc, ← exp_add]; simp
    _ ≤ C 0 * exp (-μ * t) := mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le

/-- After a bolus with `Vmax > 0` the concentration washes out to `0`. -/
theorem IsSolution.tendsto_bolus (h : IsSolution Vmax Km 0 C) (hV : 0 < Vmax) (hK : 0 < Km)
    (h0 : 0 ≤ C 0) : Tendsto C atTop (𝓝 0) := by
  have hμ : 0 < Vmax / (Km + C 0) := div_pos hV (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_amount_bolus hμ (C 0)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with t ht using h.nonneg hV.le hK le_rfl h0 ht
  · filter_upwards [eventually_ge_atTop 0] with t ht using h.le_amount_bolus hV.le hK h0 ht

/-! ### Bolus: area under the curve -/

/-- The potential `-(Km C + C² / 2) / Vmax` has derivative `C` along a bolus solution. -/
private theorem aucPotential_hasDerivAt (h : IsSolution Vmax Km 0 C) (hV : 0 < Vmax)
    (hK : 0 < Km) (h0 : 0 ≤ C 0) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun r ↦ -(Km * C r + C r ^ 2 / 2) / Vmax) (C s) s := by
  have hC := h.nonneg hV.le hK le_rfl h0 hs
  have hKC : Km + C s ≠ 0 := ne_of_gt (by linarith)
  refine ((((h s hs).const_mul Km).add (((h s hs).pow 2).div_const 2)).neg.div_const
    Vmax).congr_deriv ?_
  unfold mmRate
  field_simp
  ring

/-- **Integrated balance after a bolus.** On `[0, T]`,
`∫₀ᵀ C = (Km (C₀ - C(T)) + (C₀² - C(T)²) / 2) / Vmax`. -/
theorem IsSolution.integral_bolus (h : IsSolution Vmax Km 0 C) (hV : 0 < Vmax) (hK : 0 < Km)
    (h0 : 0 ≤ C 0) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0)..T, C t = (Km * (C 0 - C T) + (C 0 ^ 2 - C T ^ 2) / 2) / Vmax := by
  have hd : ∀ s ∈ uIcc 0 T, HasDerivAt (fun r ↦ -(Km * C r + C r ^ 2 / 2) / Vmax) (C s) s :=
    fun s hs ↦ aucPotential_hasDerivAt h hV hK h0 (by rw [uIcc_of_le hT] at hs; exact hs.1)
  have hcont : ContinuousOn C (uIcc 0 T) := fun s hs ↦
    (h s (by rw [uIcc_of_le hT] at hs; exact hs.1)).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  ring

/-- The potential `-(Km C + C² / 2) / Vmax` tends to `0` along a bolus solution. -/
private theorem aucPotential_tendsto (h : IsSolution Vmax Km 0 C) (hV : 0 < Vmax)
    (hK : 0 < Km) (h0 : 0 ≤ C 0) :
    Tendsto (fun r ↦ -(Km * C r + C r ^ 2 / 2) / Vmax) atTop (𝓝 0) := by
  have hlim := h.tendsto_bolus hV hK h0
  simpa using (((hlim.const_mul Km).add ((hlim.pow 2).div_const 2)).neg).div_const Vmax

/-- **The bolus AUC is finite.** For `Vmax, Km > 0` and `C(0) ≥ 0`, a bolus solution is
integrable on `(0, ∞)`. (This makes `IsSolution.integral_Ioi_bolus` a statement about a
convergent integral, not the Bochner default `0`.) -/
theorem IsSolution.integrableOn_Ioi_bolus (h : IsSolution Vmax Km 0 C) (hV : 0 < Vmax)
    (hK : 0 < Km) (h0 : 0 ≤ C 0) : IntegrableOn C (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun _ hs ↦ aucPotential_hasDerivAt h hV hK h0 hs)
    (fun _ hs ↦ h.nonneg hV.le hK le_rfl h0 (le_of_lt hs)) (aucPotential_tendsto h hV hK h0)

/-- **Bolus AUC.** For `Vmax, Km > 0` and `C(0) ≥ 0`, the total area under the curve is
`∫₀^∞ C = C₀ (Km + C₀ / 2) / Vmax` (a convergent integral, `IsSolution.integrableOn_Ioi_bolus`). -/
theorem IsSolution.integral_Ioi_bolus (h : IsSolution Vmax Km 0 C) (hV : 0 < Vmax)
    (hK : 0 < Km) (h0 : 0 ≤ C 0) : ∫ t in Ioi 0, C t = bolusAUC Vmax Km (C 0) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun s hs ↦ aucPotential_hasDerivAt h hV hK h0 hs)
    (fun s hs ↦ h.nonneg hV.le hK le_rfl h0 (le_of_lt hs)) (aucPotential_tendsto h hV hK h0),
    bolusAUC]
  ring

/-! ### Dose–AUC nonlinearity -/

/-- **AUC splits into a linear and a saturation part.** For a bolus of dose `V C₀` into volume
`V > 0`, the saturable AUC is the AUC of the linear model with clearance `CL = V Vmax / Km`
(`CompartmentKinetics`, value `D / CL = C₀ Km / Vmax`) plus `C₀² / (2 Vmax)`. -/
theorem bolusAUC_eq_integral_linear_add (hV : 0 < Vmax) (hK : 0 < Km) {V : ℝ} (hVol : 0 < V)
    (C₀ : ℝ) : bolusAUC Vmax Km C₀ =
      (∫ t in Ici 0, concentration (V * Vmax / Km) V 0 (V * C₀) t) + C₀ ^ 2 / (2 * Vmax) := by
  rw [integral_Ici_concentration_bolus (by positivity) hVol, bolusAUC]
  field_simp

/-- **Superproportionality.** Doubling a positive dose more than doubles the AUC. -/
theorem two_mul_bolusAUC_lt (hV : 0 < Vmax) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    2 * bolusAUC Vmax Km C₀ < bolusAUC Vmax Km (2 * C₀) := by
  have : bolusAUC Vmax Km (2 * C₀) - 2 * bolusAUC Vmax Km C₀ = C₀ ^ 2 / Vmax := by
    unfold bolusAUC; ring
  have : 0 < C₀ ^ 2 / Vmax := by positivity
  linarith

/-- The dose-normalized AUC is `(Km + C₀ / 2) / Vmax`. -/
theorem bolusAUC_div {C₀ : ℝ} (hC₀ : C₀ ≠ 0) :
    bolusAUC Vmax Km C₀ / C₀ = (Km + C₀ / 2) / Vmax := by
  unfold bolusAUC
  field_simp

/-- The dose-normalized AUC `AUC / C₀` is strictly increasing in the dose. -/
theorem strictMonoOn_bolusAUC_div (hV : 0 < Vmax) :
    StrictMonoOn (fun C₀ ↦ bolusAUC Vmax Km C₀ / C₀) (Ioi 0) := by
  intro a ha b hb hab
  simp only [bolusAUC_div (ne_of_gt ha), bolusAUC_div (ne_of_gt hb)]
  exact div_lt_div_of_pos_right (by linarith) hV

/-- **AUC is not proportional to dose** for `Vmax > 0`: there is no constant `a` with
`AUC(C₀) = a C₀` for all `C₀ ≥ 0`. (For linear elimination `AUC = D / CL` is proportional,
`CompartmentKinetics.integral_Ici_concentration_bolus`.) -/
theorem not_exists_bolusAUC_eq_mul (hV : 0 < Vmax) :
    ¬ ∃ a, ∀ C₀, 0 ≤ C₀ → bolusAUC Vmax Km C₀ = a * C₀ := by
  rintro ⟨a, ha⟩
  have h1 := ha 1 zero_le_one
  have h2 := ha 2 zero_le_two
  unfold bolusAUC at h1 h2
  field_simp at h1 h2
  nlinarith

/-- **Low-dose limit.** As the dose tends to `0` the dose-normalized AUC tends to `Km / Vmax`,
the value `1 / k` of the linear model with `k = Vmax / Km`. -/
theorem tendsto_bolusAUC_div (Vmax Km : ℝ) :
    Tendsto (fun C₀ ↦ bolusAUC Vmax Km C₀ / C₀) (𝓝[>] 0) (𝓝 (Km / Vmax)) := by
  have hc : Tendsto (fun C₀ : ℝ ↦ (Km + C₀ / 2) / Vmax) (𝓝[>] 0) (𝓝 ((Km + 0 / 2) / Vmax)) :=
    ((continuous_const.add (continuous_id.div_const 2)).div_const
      Vmax).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [zero_div, add_zero] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with C₀ hC₀
  exact (bolusAUC_div (ne_of_gt hC₀)).symm

/-! ### Constant infusion: steady state -/

/-- A constant `c` is a solution iff elimination balances infusion, `mmRate Vmax Km c = R`. -/
theorem isSolution_const_iff {c : ℝ} :
    IsSolution Vmax Km R (fun _ ↦ c) ↔ mmRate Vmax Km c = R := by
  constructor
  · intro h
    have := (h 0 le_rfl).unique (hasDerivAt_const 0 c)
    linarith
  · intro h t _
    rw [h, sub_self]
    exact hasDerivAt_const t c

/-- The steady state is nonnegative for `0 ≤ R < Vmax`, `Km ≥ 0`. -/
theorem steadyConc_nonneg (hK : 0 ≤ Km) (hR : 0 ≤ R) (hRV : R < Vmax) :
    0 ≤ steadyConc Vmax Km R :=
  div_nonneg (mul_nonneg hR hK) (sub_pos.2 hRV).le

/-- For `R < Vmax` elimination at `C∞ = R Km / (Vmax - R)` balances the infusion. -/
theorem mmRate_steadyConc (hV : 0 < Vmax) (hK : 0 < Km) (hRV : R < Vmax) :
    mmRate Vmax Km (steadyConc Vmax Km R) = R := by
  have h1 : Vmax - R ≠ 0 := (sub_pos.2 hRV).ne'
  have h2 : Km + R * Km / (Vmax - R) = Km * Vmax / (Vmax - R) := by
    field_simp
    ring
  unfold mmRate steadyConc
  rw [h2]
  field_simp

/-- **Steady state.** For `0 ≤ R < Vmax` the constant `C∞` is a solution. -/
theorem isSolution_steadyConc (hV : 0 < Vmax) (hK : 0 < Km) (hRV : R < Vmax) :
    IsSolution Vmax Km R (fun _ ↦ steadyConc Vmax Km R) :=
  isSolution_const_iff.2 (mmRate_steadyConc hV hK hRV)

/-- **Uniqueness of the steady state.** For `R < Vmax` the only nonnegative balance point is
`C∞`. -/
theorem eq_steadyConc_of_mmRate_eq (hK : 0 < Km) (hRV : R < Vmax) {c : ℝ} (hc : 0 ≤ c)
    (h : mmRate Vmax Km c = R) : c = steadyConc Vmax Km R := by
  unfold mmRate at h
  unfold steadyConc
  rw [div_eq_iff (ne_of_gt (by linarith))] at h
  rw [eq_div_iff (sub_pos.2 hRV).ne']
  linear_combination h

/-- **No steady state when infusion reaches capacity.** For `0 < Vmax ≤ R` no nonnegative
constant is a solution. -/
theorem not_isSolution_const_of_le (hV : 0 < Vmax) (hK : 0 < Km) (hVR : Vmax ≤ R) {c : ℝ}
    (hc : 0 ≤ c) : ¬ IsSolution Vmax Km R (fun _ ↦ c) := by
  rw [isSolution_const_iff]
  exact ((mmRate_lt hV hK hc).trans_le hVR).ne

/-- **Unbounded accumulation.** For `R > Vmax ≥ 0` every solution with `C(0) ≥ 0` tends to
`∞`. -/
theorem IsSolution.tendsto_atTop (h : IsSolution Vmax Km R C) (hV : 0 ≤ Vmax) (hK : 0 < Km)
    (hVR : Vmax < R) (h0 : 0 ≤ C 0) : Tendsto C atTop atTop := by
  refine tendsto_atTop_mono' _ ?_
    (tendsto_atTop_add_const_left _ (C 0) (tendsto_id.const_mul_atTop (sub_pos.2 hVR)))
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact h.add_mul_le hV hK (hV.trans hVR.le) h0 ht

/-- **Exponential approach to the steady state.** For `0 ≤ R < Vmax`, `Km > 0` and
`C(0) ≥ 0`, with `x₀ = C(0) - C∞` and `λ = (Vmax - R) / (Km + C∞ + |x₀|)`,
`|C(t) - C∞| ≤ |x₀| e^{-λ t}`. -/
theorem IsSolution.abs_sub_steadyConc_le (h : IsSolution Vmax Km R C) (hK : 0 < Km)
    (hR : 0 ≤ R) (hRV : R < Vmax) (h0 : 0 ≤ C 0) (ht : 0 ≤ t) :
    |C t - steadyConc Vmax Km R| ≤ |C 0 - steadyConc Vmax Km R| *
      exp (-((Vmax - R) / (Km + steadyConc Vmax Km R + |C 0 - steadyConc Vmax Km R|)) * t) := by
  have hV : 0 ≤ Vmax := hR.trans hRV.le
  set c := steadyConc Vmax Km R with hc
  set a := Vmax - R with ha
  have hapos : 0 < a := sub_pos.2 hRV
  have hc0 : 0 ≤ c := steadyConc_nonneg hK.le hR hRV
  have hnn : ∀ s, 0 ≤ s → 0 ≤ C s := fun s hs ↦ h.nonneg hV hK hR h0 hs
  have hx : ∀ s, 0 ≤ s → HasDerivAt (fun r ↦ C r - c) (-a * (C s - c) / (Km + C s)) s := by
    intro s hs
    rw [← sub_mmRate_eq (ne_of_gt (by linarith [hnn s hs])) hapos.ne']
    exact (h s hs).sub_const c
  -- Step 1: `(C - c)²` does not increase, so `C ≤ c + |x₀|`.
  have hsq : ∀ s, 0 ≤ s → (C s - c) ^ 2 ≤ (C 0 - c) ^ 2 := by
    intro s hs
    have := le_of_hasDerivAt_nonneg (g := fun r ↦ -(C r - c) ^ 2)
      (g' := fun r ↦ 2 * a * (C r - c) ^ 2 / (Km + C r))
      (fun r hr ↦ by
        have hKC : Km + C r ≠ 0 := ne_of_gt (by linarith [hnn r hr])
        refine ((hx r hr).pow 2).neg.congr_deriv ?_
        field_simp
        ring)
      (fun r hr ↦ div_nonneg (by positivity) (by linarith [hnn r hr])) le_rfl hs
    linarith
  set M := Km + c + |C 0 - c| with hM
  have hMpos : 0 < M := by positivity
  have hle : ∀ s, 0 ≤ s → Km + C s ≤ M := by
    intro s hs
    have := sq_le_sq.mp (hsq s hs)
    have := le_abs_self (C s - c)
    linarith [abs_nonneg (C 0 - c)]
  -- Step 2: `(C - c)² e^{2 λ t}` does not increase.
  set lam := a / M with hlam
  have hexp := le_of_hasDerivAt_nonneg (g := fun r ↦ -((C r - c) ^ 2 * exp (2 * lam * r)))
    (g' := fun r ↦ 2 * (C r - c) ^ 2 * (a / (Km + C r) - lam) * exp (2 * lam * r))
    (fun r hr ↦ by
      have hKC : Km + C r ≠ 0 := ne_of_gt (by linarith [hnn r hr])
      refine (((hx r hr).pow 2).mul ((hasDerivAt_id' r).const_mul (2 * lam)).exp).neg.congr_deriv
        ?_
      simp only [Pi.pow_apply]
      field_simp
      ring)
    (fun r hr ↦ by
      have h1 : lam ≤ a / (Km + C r) :=
        div_le_div_of_nonneg_left hapos.le (by linarith [hnn r hr]) (hle r hr)
      have := exp_pos (2 * lam * r)
      have : 0 ≤ a / (Km + C r) - lam := by linarith
      positivity)
    le_rfl ht
  simp only [mul_zero, exp_zero, mul_one, neg_le_neg_iff] at hexp
  have hgoal : (C t - c) ^ 2 ≤ ((C 0 - c) * exp (-lam * t)) ^ 2 :=
    calc (C t - c) ^ 2 = (C t - c) ^ 2 * exp (2 * lam * t) * exp (-(2 * lam * t)) := by
          rw [mul_assoc, ← exp_add]; simp
      _ ≤ (C 0 - c) ^ 2 * exp (-(2 * lam * t)) :=
          mul_le_mul_of_nonneg_right hexp (exp_pos _).le
      _ = ((C 0 - c) * exp (-lam * t)) ^ 2 := by
          rw [mul_pow, sq (exp _), ← exp_add]
          congr 2
          ring
  have := sq_le_sq.mp hgoal
  rwa [abs_mul, abs_of_pos (exp_pos _)] at this

/-- **Convergence to the steady state.** For `0 ≤ R < Vmax`, `Km > 0` and `C(0) ≥ 0` every
solution tends to `C∞ = R Km / (Vmax - R)`. -/
theorem IsSolution.tendsto_steadyConc (h : IsSolution Vmax Km R C) (hK : 0 < Km) (hR : 0 ≤ R)
    (hRV : R < Vmax) (h0 : 0 ≤ C 0) : Tendsto C atTop (𝓝 (steadyConc Vmax Km R)) := by
  set c := steadyConc Vmax Km R
  have hlam : 0 < (Vmax - R) / (Km + c + |C 0 - c|) :=
    div_pos (sub_pos.2 hRV) (by have := steadyConc_nonneg hK.le hR hRV; positivity)
  have hexp : Tendsto (fun t ↦ |C 0 - c| *
      exp (-((Vmax - R) / (Km + c + |C 0 - c|)) * t)) atTop (𝓝 0) := by
    simpa using (tendsto_amount_bolus hlam |C 0 - c|).congr fun t ↦ amount_bolus _ _ _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hexp
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact h.abs_sub_steadyConc_le hK hR hRV h0 ht

end MathlibExt.Biology.Biophysics.SaturableElimination
