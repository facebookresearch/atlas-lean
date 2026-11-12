/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gas equations of state: ideal gas, van der Waals, virial

Dalton partial pressures, the van der Waals critical point and reduced equation, and the exact
van der Waals virial identity with its Boyle temperature, each proved inside its named model.

## i. Overview

Each result is a mathematical consequence *inside* a named model; no model is derived here.
The definitions (`partialPressure`, `vdWPressure`, `compressibilityFactor`, the van der Waals
reduced variables and `vdWSecondVirialCoeff`) are mathematical definitions; the three models
below are model assumptions; every lemma and theorem names, in its docstring, the model it
lives in.

* Ideal-gas model: `p V = n R T` is an idealization (the `p → 0` limit of a real gas). It is a
  model assumption, never derived from mathematics.
* Van der Waals model: `p = R T / (V_m - b) - a / V_m ^ 2` on `V_m > b`, where `a, b > 0` are
  fitted (empirical) parameters.
* First-order (truncated) virial model: `Z ≈ 1 + B(T) / V_m` with a fitted coefficient `B(T)`;
  the truncation is never stated as an equality here. For the van der Waals gas
  `B(T) = b - a / (R T)`, and the virial identity below keeps the exact remainder
  `b ^ 2 / (V_m (V_m - b))` instead of truncating.

All quantities are plain real numbers: `p, Vm, T, R, a, b` carry the consistent units of the
model after a fixed unit choice, and no dimensional quantity type is introduced here.

Below the critical temperature an isotherm has a local minimum and a local maximum in `V_m > b`;
for positive pressures between them the cubic in `V_m` has three real roots `V_m > b`, the
middle one on the unphysical (mechanically unstable) branch. The Maxwell equal-area construction
is elective and is NOT included here. The reduced equation is parameter-free exactly within the
van der Waals model; for real gases the law of corresponding states is an empirical regularity,
not a theorem.

Reuse-verified against Mathlib / ATLAS main: this module imports no next-50 prerequisite module.

## ii. Key results

- `Chemistry.GasEquations.sum_partialPressure` : partial pressures `x_i p` add up to `p`.
- `Chemistry.GasEquations.idealGas_pressure_alone_eq_partialPressure` : in the ideal-gas model,
  the pressure of a component alone equals its Dalton partial pressure.
- `Chemistry.GasEquations.hasDerivAt_vdWPressure`,
  `Chemistry.GasEquations.hasDerivAt_deriv_vdWPressure` : the first and second derivatives of
  the van der Waals pressure in the molar volume.
- `Chemistry.GasEquations.vdW_critical_point`,
  `Chemistry.GasEquations.vdW_critical_point_of_deriv` : the critical equations force
  `V_m = 3 b`, `T = 8 a / (27 R b)`, `p = a / (27 b ^ 2)` and `Z = 3 / 8`.
- `Chemistry.GasEquations.reduced_vdW_equation` : `(P_r + 3 / V_r ^ 2) (3 V_r - 1) = 8 T_r`.
- `Chemistry.GasEquations.vdW_virial_expansion` : `Z = 1 + B / V_m + b ^ 2 / (V_m (V_m - b))`.
- `Chemistry.GasEquations.vdWSecondVirialCoeff_eq_zero_iff` : the Boyle temperature
  `T = a / (R b)`.

## iii. Table of contents

- A. Dalton partial pressures
- B. The van der Waals pressure and its derivatives
- C. The van der Waals critical point
- D. The reduced van der Waals equation
- E. Virial coefficients and the Boyle temperature

## iv. References

- OpenStax, *Chemistry 2e*, Chapter 9 (Gases), as the chapter-level curriculum anchor.
- IUPAC, *Quantities, Units and Symbols in Physical Chemistry* (the Green Book), for the
  quantity symbols.
-/

@[expose] public section

namespace Chemistry

namespace GasEquations

/-! ## A. Dalton partial pressures -/

/-- The partial pressure `p_i = x_i p` of a component with mole fraction `x_i` in a mixture at
total pressure `p`. -/
def partialPressure (x_i p : ℝ) : ℝ := x_i * p

/-- Dalton's sum: if the mole fractions `x i` add up to `1`, the partial pressures add up to the
total pressure `p`. This uses no model assumption, only the definition `p_i = x_i p`. -/
lemma sum_partialPressure {ι : Type*} [Fintype ι] (x : ι → ℝ) (p : ℝ) (hx : ∑ i, x i = 1) :
    ∑ i, partialPressure (x i) p = p := by
  simp only [partialPressure, ← Finset.sum_mul, hx, one_mul]

/-- Ideal-gas model: in a mixture with amounts `n i` and total amount `N = ∑ i, n i` at volume `V`
and temperature `T`, the pressure `n i * R * T / V` that component `i` would exert alone at the
same `T, V` (this is the definition of the alone-pressure) equals its partial pressure
`x_i p` with mole fraction `x_i = n i / N` and total pressure `p = N * R * T / V`. The hypotheses
prefixed with `_` record the domain of the model and are not used by the proof. -/
lemma idealGas_pressure_alone_eq_partialPressure {ι : Type*} [Fintype ι] (n : ι → ℝ)
    (N V T R : ℝ) (hN : 0 < N) (_hNsum : N = ∑ i, n i) (hV : 0 < V) (_hT : 0 < T)
    (_hR : 0 < R) (i : ι) :
    n i * R * T / V = partialPressure (n i / N) (N * R * T / V) := by
  rw [partialPressure]
  field_simp

/-! ## B. The van der Waals pressure and its derivatives -/

/-- The van der Waals pressure `p = R T / (V_m - b) - a / V_m ^ 2` as a function of the molar
volume `Vm`. The model is used on `Vm > b` with fitted parameters `a, b > 0` and with
`R, T > 0`; outside `Vm > b` no van der Waals result of this module applies. -/
noncomputable def vdWPressure (a b R T Vm : ℝ) : ℝ := R * T / (Vm - b) - a / Vm ^ 2

/-- Van der Waals model: the derivative of the pressure in the molar volume at any
`Vm > b > 0` is `∂p/∂V_m = -R T / (V_m - b) ^ 2 + 2 a / V_m ^ 3`. -/
lemma hasDerivAt_vdWPressure (a b R T Vm : ℝ) (hb : 0 < b) (hVm : b < Vm) :
    HasDerivAt (fun V => vdWPressure a b R T V) (-R * T / (Vm - b) ^ 2 + 2 * a / Vm ^ 3) Vm := by
  have hVb : Vm - b ≠ 0 := sub_ne_zero.2 hVm.ne'
  have hV : Vm ≠ 0 := (hb.trans hVm).ne'
  unfold vdWPressure
  have h₁ := (hasDerivAt_const Vm (R * T)).fun_div ((hasDerivAt_id' Vm).sub_const b) hVb
  have h₂ := (hasDerivAt_const Vm a).fun_div (hasDerivAt_pow 2 Vm) (pow_ne_zero 2 hV)
  refine (h₁.fun_sub h₂).congr_deriv ?_
  field_simp
  ring

/-- Van der Waals model: the second derivative of the pressure in the molar volume at any
`Vm > b > 0`, i.e. the derivative of `deriv p`, is `2 R T / (V_m - b) ^ 3 - 6 a / V_m ^ 4`. -/
lemma hasDerivAt_deriv_vdWPressure (a b R T Vm : ℝ) (hb : 0 < b) (hVm : b < Vm) :
    HasDerivAt (deriv fun V => vdWPressure a b R T V)
      (2 * R * T / (Vm - b) ^ 3 - 6 * a / Vm ^ 4) Vm := by
  have hVb : Vm - b ≠ 0 := sub_ne_zero.2 hVm.ne'
  have hV : Vm ≠ 0 := (hb.trans hVm).ne'
  have h₁ := (hasDerivAt_const Vm (-R * T)).fun_div
    (((hasDerivAt_id' Vm).sub_const b).fun_pow 2) (pow_ne_zero 2 hVb)
  have h₂ := (hasDerivAt_const Vm (2 * a)).fun_div (hasDerivAt_pow 3 Vm) (pow_ne_zero 3 hV)
  have h : HasDerivAt (fun V => -R * T / (V - b) ^ 2 + 2 * a / V ^ 3)
      (2 * R * T / (Vm - b) ^ 3 - 6 * a / Vm ^ 4) Vm := by
    refine (h₁.fun_add h₂).congr_deriv ?_
    field_simp
    ring
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hVm] with V hV'
  exact (hasDerivAt_vdWPressure a b R T V hb hV').deriv

/-! ## C. The van der Waals critical point -/

/-- The compressibility factor `Z = p V_m / (R T)`. -/
noncomputable def compressibilityFactor (p Vm R T : ℝ) : ℝ := p * Vm / (R * T)

/-- Van der Waals model, critical point. If `a, b, R, T > 0`, `Vm > b`, and both critical
equations `∂p/∂V_m = 0` and `∂²p/∂V_m² = 0` hold at `(Vm, T)` (in the explicit forms given by
`hasDerivAt_vdWPressure` and `hasDerivAt_deriv_vdWPressure`), then the critical molar volume is
`Vm = 3 b`, the critical temperature is `T = 8 a / (27 R b)`, the critical pressure is
`a / (27 b ^ 2)` and the critical compressibility factor is `3 / 8`.

Below the critical temperature, for positive pressures between the local extrema of an isotherm,
the van der Waals cubic has three real roots `V_m > b`, the middle one on an unphysical branch;
the Maxwell construction is elective and is not included here. -/
theorem vdW_critical_point (a b R T Vm : ℝ) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hT : 0 < T) (hVm : b < Vm) (h₁ : -R * T / (Vm - b) ^ 2 + 2 * a / Vm ^ 3 = 0)
    (h₂ : 2 * R * T / (Vm - b) ^ 3 - 6 * a / Vm ^ 4 = 0) :
    Vm = 3 * b ∧ T = 8 * a / (27 * R * b) ∧ vdWPressure a b R T Vm = a / (27 * b ^ 2) ∧
      compressibilityFactor (vdWPressure a b R T Vm) Vm R T = 3 / 8 := by
  have hVb : Vm - b ≠ 0 := sub_ne_zero.2 hVm.ne'
  have hV : Vm ≠ 0 := (hb.trans hVm).ne'
  rw [div_add_div _ _ (pow_ne_zero 2 hVb) (pow_ne_zero 3 hV),
    div_eq_iff (mul_ne_zero (pow_ne_zero 2 hVb) (pow_ne_zero 3 hV))] at h₁
  rw [div_sub_div _ _ (pow_ne_zero 3 hVb) (pow_ne_zero 4 hV),
    div_eq_iff (mul_ne_zero (pow_ne_zero 3 hVb) (pow_ne_zero 4 hV))] at h₂
  have hVc : Vm = 3 * b := by
    have h : R * T * Vm ^ 3 * (3 * b - Vm) = 0 := by
      linear_combination h₂ + 3 * (Vm - b) * h₁
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (mul_ne_zero (mul_ne_zero hR.ne' hT.ne') (pow_ne_zero 3 hV))
    · linarith
  subst hVc
  have hTc : T = 8 * a / (27 * R * b) := by
    rw [eq_div_iff (by positivity)]
    refine mul_left_cancel₀ (pow_ne_zero 2 hb.ne') ?_
    linear_combination -h₁
  have hp : vdWPressure a b R T (3 * b) = a / (27 * b ^ 2) := by
    rw [vdWPressure, hTc, show 3 * b - b = 2 * b by ring]
    field_simp
    ring
  refine ⟨rfl, hTc, hp, ?_⟩
  rw [compressibilityFactor, hp, hTc]
  field_simp

/-- Van der Waals model, critical point stated with the derivatives themselves: if
`deriv p = 0` and `deriv (deriv p) = 0` at `Vm > b` for the van der Waals pressure `p`, then
`Vm = 3 b`, `T = 8 a / (27 R b)`, `p = a / (27 b ^ 2)` and `Z = 3 / 8`. -/
lemma vdW_critical_point_of_deriv (a b R T Vm : ℝ) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hT : 0 < T) (hVm : b < Vm) (h₁ : deriv (fun V => vdWPressure a b R T V) Vm = 0)
    (h₂ : deriv (deriv fun V => vdWPressure a b R T V) Vm = 0) :
    Vm = 3 * b ∧ T = 8 * a / (27 * R * b) ∧ vdWPressure a b R T Vm = a / (27 * b ^ 2) ∧
      compressibilityFactor (vdWPressure a b R T Vm) Vm R T = 3 / 8 := by
  rw [(hasDerivAt_vdWPressure a b R T Vm hb hVm).deriv] at h₁
  rw [(hasDerivAt_deriv_vdWPressure a b R T Vm hb hVm).deriv] at h₂
  exact vdW_critical_point a b R T Vm ha hb hR hT hVm h₁ h₂

/-! ## D. The reduced van der Waals equation -/

/-- The van der Waals reduced pressure `P_r = p / p_c` with the critical pressure
`p_c = a / (27 b ^ 2)`. -/
noncomputable def vdWReducedPressure (a b p : ℝ) : ℝ := p / (a / (27 * b ^ 2))

/-- The van der Waals reduced molar volume `V_r = V_m / V_{m,c}` with the critical molar volume
`V_{m,c} = 3 b`. -/
noncomputable def vdWReducedVolume (b Vm : ℝ) : ℝ := Vm / (3 * b)

/-- The van der Waals reduced temperature `T_r = T / T_c` with the critical temperature
`T_c = 8 a / (27 R b)`. -/
noncomputable def vdWReducedTemperature (a b R T : ℝ) : ℝ := T / (8 * a / (27 * R * b))

/-- Van der Waals model: the reduced equation `(P_r + 3 / V_r ^ 2) (3 V_r - 1) = 8 T_r`, in which
`a, b, R` no longer appear. This is exact within the van der Waals model; for real gases the law
of corresponding states is an empirical regularity. The hypotheses `_hR` and `_hT` record the
domain of the model; the identity holds for every `R` and `T`. -/
theorem reduced_vdW_equation (a b R T Vm p Pr Vr Tr : ℝ) (ha : 0 < a) (hb : 0 < b)
    (_hR : 0 < R) (_hT : 0 < T) (hVm : b < Vm) (hp : p = vdWPressure a b R T Vm)
    (hPr : Pr = vdWReducedPressure a b p) (hVr : Vr = vdWReducedVolume b Vm)
    (hTr : Tr = vdWReducedTemperature a b R T) :
    (Pr + 3 / Vr ^ 2) * (3 * Vr - 1) = 8 * Tr := by
  have hVb : Vm - b ≠ 0 := sub_ne_zero.2 hVm.ne'
  have hV : Vm ≠ 0 := (hb.trans hVm).ne'
  subst hp hPr hVr hTr
  rw [vdWReducedPressure, vdWReducedVolume, vdWReducedTemperature, vdWPressure]
  field_simp
  ring

/-! ## E. Virial coefficients and the Boyle temperature -/

/-- The second virial coefficient `B(T) = b - a / (R T)` of the van der Waals gas. -/
noncomputable def vdWSecondVirialCoeff (a b R T : ℝ) : ℝ := b - a / (R * T)

/-- Van der Waals model, exact virial identity: `Z = 1 + B / V_m + b ^ 2 / (V_m (V_m - b))` with
`B = b - a / (R T)`. So `B` is the coefficient of `1 / V_m` in the expansion of `Z`, with the
exact remainder `b ^ 2 / (V_m (V_m - b))`, which is of order `1 / V_m ^ 2` as `V_m → ∞` (that
asymptotic remark is not formalized here); the truncation `Z ≈ 1 + B / V_m` is not an equality.
The hypothesis `_ha` records the domain of the model; the identity holds for every `a`. -/
theorem vdW_virial_expansion (a b R T Vm p : ℝ) (_ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hT : 0 < T) (hVm : b < Vm) (hp : p = vdWPressure a b R T Vm) :
    compressibilityFactor p Vm R T =
      1 + vdWSecondVirialCoeff a b R T / Vm + b ^ 2 / (Vm * (Vm - b)) := by
  have hVb : Vm - b ≠ 0 := sub_ne_zero.2 hVm.ne'
  have hV : Vm ≠ 0 := (hb.trans hVm).ne'
  subst hp
  rw [compressibilityFactor, vdWSecondVirialCoeff, vdWPressure]
  field_simp
  ring

/-- Van der Waals model, Boyle temperature: for `a, b, R > 0` the second virial coefficient
`B(T) = b - a / (R T)` vanishes exactly at `T = a / (R b)`. -/
theorem vdWSecondVirialCoeff_eq_zero_iff (a b R T : ℝ) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    vdWSecondVirialCoeff a b R T = 0 ↔ T = a / (R * b) := by
  rw [vdWSecondVirialCoeff, sub_eq_zero]
  constructor
  · intro h
    have hT : T ≠ 0 := by
      rintro rfl
      rw [mul_zero, div_zero] at h
      exact hb.ne' h
    rw [eq_div_iff (mul_ne_zero hR.ne' hb.ne')]
    rw [eq_div_iff (mul_ne_zero hR.ne' hT)] at h
    linear_combination h
  · rintro rfl
    field_simp

end GasEquations

end Chemistry
