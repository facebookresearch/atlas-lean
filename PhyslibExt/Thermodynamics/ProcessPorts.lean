/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Thermodynamics.FirstLaw

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PhyslibExt.Chemistry.Thermodynamics.Thermochemistry

/-!
# Process ports: the engineering work-out sign adapter

## i. Overview

The first law in `PhyslibExt.Chemistry.Thermodynamics.FirstLaw` uses the IUPAC convention
`ΔU = q + w`, where `w` is the work done on the system. Engineering texts write
`ΔU = Q_in - W_out` with `W_out` the work done by the system. This file names the adapter
`workOut w = -w` (heat keeps its sign, `Q_in = q`) and transports the existing closed-process
results through it: the constant-`Cv` energy balance (`internalEnergy_sub`), reversible
isothermal work (`isothermal_work`) and the irreversible-versus-reversible comparison
(`irreversible_le_reversible`). No first law, equation of state or work integral is restated;
the IUPAC sign of the existing declarations is unchanged.

Molar versus mass-specific units: a gas of `n` moles with molar mass `M` has mass `m = n * M`
and specific gas constant `Rs = R / M`, so the ideal-gas coefficient is `n * R = m * Rs`. The
existing declarations use only that product, so mass-specific work takes `(m, Rs)` in the slots
of `(n, R)`, and the adiabatic pressure ratio is `idealGasP_ratio_of_log_relation` with
coefficient `k = m * Rs`.

Variable heat capacity: when the internal energy `U` has temperature derivative `Cv T`, the
energy change `U T₂ = U T₁ + ∫ T in T₁..T₂, Cv T` is `kirchhoff_law` of
`PhyslibExt.Chemistry.Thermodynamics.Thermochemistry` applied with `U` in place of the enthalpy,
and the results of sections D and E are derived from it. The engineering balance is
`Q_in - W_out = ∫ Cv`. A continuous positive `Cv` makes `U` strictly increasing. For the linear
model `Cv T = a + b * T` the exact change minus the endpoint estimate `Cv T₁ * (T₂ - T₁)` is the
signed amount `b * (T₂ - T₁) ^ 2 / 2`: for `T₁ ≠ T₂` its sign is that of `b`, and at `T₁ = T₂` it
is zero. No heat-capacity fit is claimed and `Cv` is never inferred from a substance.

Model inputs: the ideal-gas equation of state and the first law as encoded by the existing
declarations; temperatures are absolute (`T > 0`); volumes, amounts, masses and gas constants
are positive where a result says so. Each result assumes only the hypotheses its proof uses.
Celsius readings are affine and are never valid temperatures inside ratios or logarithms.

## ii. Key results

- `ProcessPorts.firstLaw_iff_workOut`: `ΔU = q + w ↔ ΔU = q - workOut w`.
- `ProcessPorts.workOut_isothermalWorkOn`: `∫ p dV = W_out = n R T log (V₂ / V₁)`.
- `ProcessPorts.workOut_irreversible_le_reversible`: `0 ≤ W_out,irr ≤ W_out,rev`.
- `ProcessPorts.idealGasP_ratio_of_specific_log_relation`: the adiabat with `k = m * Rs`.
- `ProcessPorts.heat_sub_workOut_eq_integral`: `Q_in - W_out = ∫ T in T₁..T₂, Cv T`.
- `ProcessPorts.strictMonoOn_of_heatCapacity_pos`: continuous `Cv > 0` gives strict increase.
- `ProcessPorts.sub_ne_endpoint_of_linear_heatCapacity`: the endpoint estimate is not exact.

## iii. Table of contents

- A. The work-out sign adapter
- B. Isothermal expansion work
- C. Molar and mass-specific coefficients
- D. Variable heat capacity
- E. Linear heat capacity versus the endpoint estimate

## iv. References

- E. R. Cohen et al., *Quantities, Units and Symbols in Physical Chemistry* (IUPAC Green Book),
  3rd ed., 2007: `ΔU = q + w` with `w` the work done on the system.
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 4:
  `ΔU = Q_in - W_out`, boundary work `W_b = m R T ln (V₂ / V₁)` of an isothermal ideal gas, and
  `Δu = ∫ cv(T) dT` for temperature-dependent specific heats.
- P. Atkins and J. de Paula, *Atkins' Physical Chemistry*, Chapter 2: Kirchhoff's law, the
  temperature dependence of an enthalpy change through `∫ ΔCp dT`.
-/

@[expose] public section

namespace ProcessPorts

open Chemistry.Thermodynamics

/-! ## A. The work-out sign adapter -/

/-- Work done by the system (engineering `W_out`) for the work `w` done on the system in the
IUPAC first law `ΔU = q + w`: `W_out = -w`. Heat keeps its sign, `Q_in = q`. -/
def workOut (w : ℝ) : ℝ := -w

/-- The engineering first law `ΔU = Q_in - W_out` is the IUPAC law `ΔU = q + w` read with
`Q_in = q` and `W_out = workOut w`. -/
lemma firstLaw_iff_workOut (ΔU q w : ℝ) : ΔU = q + w ↔ ΔU = q - workOut w := by
  simp only [workOut, sub_neg_eq_add]

/-- Work done on the system and work done by it differ for every nonzero work. -/
lemma workOut_ne_self {w : ℝ} (hw : w ≠ 0) : workOut w ≠ w := by
  simp only [workOut]
  intro h
  apply hw
  linarith

/-- Closed constant-`Cv` ideal gas: if the energy change satisfies the IUPAC law `ΔU = q + w`,
the engineering balance is `Q_in - W_out = Cv * (T₂ - T₁)`, for every reference state. -/
lemma heat_sub_workOut_eq (Cv U₀ T₀ T₁ T₂ q w : ℝ)
    (hlaw : internalEnergy Cv U₀ T₀ T₂ - internalEnergy Cv U₀ T₀ T₁ = q + w) :
    q - workOut w = Cv * (T₂ - T₁) := by
  simp only [workOut, sub_neg_eq_add]
  rw [← hlaw]
  exact internalEnergy_sub Cv U₀ T₀ T₁ T₂

/-! ## B. Isothermal expansion work -/

/-- Reversible isothermal work done by the gas: `∫ p dV = W_out = n R T log (V₂ / V₁)`, the
transport of `isothermal_work` (whose integrand is `-p dV`). Only the positive volumes are
used; the physical case is `n, R, T > 0`. -/
lemma workOut_isothermalWorkOn (n R T V₁ V₂ : ℝ) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) :
    (∫ V in V₁..V₂, idealGasP n R T V ∂MeasureTheory.volume)
        = workOut (isothermalWorkOn n R T V₁ V₂) ∧
      workOut (isothermalWorkOn n R T V₁ V₂) = n * R * T * Real.log (V₂ / V₁) := by
  have h := isothermal_work n R T V₁ V₂ hV₁ hV₂
  rw [intervalIntegral.integral_neg] at h
  refine ⟨?_, ?_⟩
  · simp only [workOut]
    linarith
  · simp only [workOut, isothermalWorkOn, neg_neg]

/-- A nonzero isothermal expansion (`V₁ < V₂`, `n, R, T > 0`) has positive `W_out`, while the
work done on the gas is negative: the two conventions differ in sign. -/
lemma isothermal_expansion_workOut_pos {n R T V₁ V₂ : ℝ} (hn : 0 < n) (hR : 0 < R)
    (hT : 0 < T) (hV₁ : 0 < V₁) (hV : V₁ < V₂) :
    0 < workOut (isothermalWorkOn n R T V₁ V₂) ∧ isothermalWorkOn n R T V₁ V₂ < 0 := by
  have hlog : 0 < Real.log (V₂ / V₁) := by
    apply Real.log_pos
    rw [one_lt_div hV₁]
    exact hV
  have hpos : 0 < n * R * T := mul_pos (mul_pos hn hR) hT
  have hW : workOut (isothermalWorkOn n R T V₁ V₂) = n * R * T * Real.log (V₂ / V₁) := by
    simp only [workOut, isothermalWorkOn, neg_neg]
  have hW' : isothermalWorkOn n R T V₁ V₂ = -(n * R * T * Real.log (V₂ / V₁)) := by
    simp only [isothermalWorkOn]
  rw [hW, hW']
  exact ⟨mul_pos hpos hlog, neg_neg_of_pos (mul_pos hpos hlog)⟩

/-- Isothermal expansion against a constant admissible external pressure
`0 ≤ p_ext ≤ n R T / V₂` does nonnegative work, at most the reversible work:
`0 ≤ W_out,irr ≤ W_out,rev`. This is `irreversible_le_reversible` without absolute values. -/
lemma workOut_irreversible_le_reversible {n R T V₁ V₂ p_ext : ℝ} (hn : 0 < n) (hR : 0 < R)
    (hT : 0 < T) (hV₁ : 0 < V₁) (hV : V₁ ≤ V₂) (hp_ext : 0 ≤ p_ext)
    (hadm : p_ext ≤ n * R * T / V₂) :
    0 ≤ workOut (irreversibleWorkOn p_ext V₁ V₂) ∧
      workOut (irreversibleWorkOn p_ext V₁ V₂) ≤ workOut (isothermalWorkOn n R T V₁ V₂) := by
  have hle := irreversible_le_reversible n R T V₁ V₂ p_ext hn hR hT hV₁ hV hp_ext hadm
  have hlog_nonneg : 0 ≤ Real.log (V₂ / V₁) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hV₁, one_mul]
    exact hV
  have hirr_nn : 0 ≤ p_ext * (V₂ - V₁) := mul_nonneg hp_ext (sub_nonneg.mpr hV)
  have hrev_nn : 0 ≤ n * R * T * Real.log (V₂ / V₁) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hn) (le_of_lt hR)) (le_of_lt hT)) hlog_nonneg
  have hirr : workOut (irreversibleWorkOn p_ext V₁ V₂) = p_ext * (V₂ - V₁) := by
    simp only [workOut, irreversibleWorkOn, neg_neg]
  have hrev : workOut (isothermalWorkOn n R T V₁ V₂) = n * R * T * Real.log (V₂ / V₁) := by
    simp only [workOut, isothermalWorkOn, neg_neg]
  have hirr_abs : |irreversibleWorkOn p_ext V₁ V₂| = p_ext * (V₂ - V₁) := by
    have e : irreversibleWorkOn p_ext V₁ V₂ = -(p_ext * (V₂ - V₁)) := by
      simp only [irreversibleWorkOn]
    rw [e, abs_neg]
    exact abs_of_nonneg hirr_nn
  have hrev_abs : |isothermalWorkOn n R T V₁ V₂| = n * R * T * Real.log (V₂ / V₁) := by
    have e : isothermalWorkOn n R T V₁ V₂ = -(n * R * T * Real.log (V₂ / V₁)) := by
      simp only [isothermalWorkOn]
    rw [e, abs_neg]
    exact abs_of_nonneg hrev_nn
  rw [hirr, hrev]
  rw [hirr_abs, hrev_abs] at hle
  exact ⟨hirr_nn, hle⟩

/-! ## C. Molar and mass-specific coefficients -/

/-- The ideal-gas coefficient in molar and in mass-specific units: with mass `n * M` and
specific gas constant `R / M`, `n * R = (n * M) * (R / M)`. -/
lemma molar_coeff_eq_mass_coeff (n R : ℝ) {M : ℝ} (hM : M ≠ 0) :
    n * R = n * M * (R / M) := by
  field_simp

/-- The pressure model at mass `n * M` and specific gas constant `R / M` is the molar one. -/
lemma idealGasP_mass_eq (n R T V : ℝ) {M : ℝ} (hM : M ≠ 0) :
    idealGasP (n * M) (R / M) T V = idealGasP n R T V := by
  have h := molar_coeff_eq_mass_coeff n R hM
  simp only [idealGasP]
  rw [← h]

/-- The isothermal work at mass `n * M` and specific gas constant `R / M` is the molar one. -/
lemma isothermalWorkOn_mass_eq (n R T V₁ V₂ : ℝ) {M : ℝ} (hM : M ≠ 0) :
    isothermalWorkOn (n * M) (R / M) T V₁ V₂ = isothermalWorkOn n R T V₁ V₂ := by
  have h := molar_coeff_eq_mass_coeff n R hM
  simp only [isothermalWorkOn]
  rw [← h]

/-- Specific isothermal work: per unit mass, `W_out / m = Rs T log (v₂ / v₁)` with specific
volumes `v = V / m`. -/
lemma workOut_isothermal_div_mass (m Rs T V₁ V₂ : ℝ) (hm : m ≠ 0) :
    workOut (isothermalWorkOn m Rs T V₁ V₂) / m
      = Rs * T * Real.log ((V₂ / m) / (V₁ / m)) := by
  have hdiv : (V₂ / m) / (V₁ / m) = V₂ / V₁ := by
    by_cases hV₁ : V₁ = 0
    · subst hV₁
      simp
    · have hVm : V₁ / m ≠ 0 := div_ne_zero hV₁ hm
      field_simp
  have hW : workOut (isothermalWorkOn m Rs T V₁ V₂) = m * Rs * T * Real.log (V₂ / V₁) := by
    simp only [workOut, isothermalWorkOn, neg_neg]
  rw [hW, hdiv]
  field_simp

/-- Mass-specific adiabat: the per-mass relation `cv * log (T₂ / T₁) + Rs * log (V₂ / V₁) = 0`
with `γ - 1 = Rs / cv` gives `p₂ / p₁ = (V₁ / V₂) ^ γ` for the gas of mass `m`. This is
`idealGasP_ratio_of_log_relation` with `Cv = m * cv` and coefficient `k = m * Rs`. -/
lemma idealGasP_ratio_of_specific_log_relation {m Rs cv γ T₁ T₂ V₁ V₂ : ℝ} (hm : 0 < m)
    (hRs : 0 < Rs) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hcv : cv ≠ 0) (hγ : γ - 1 = Rs / cv)
    (had : cv * Real.log (T₂ / T₁) + Rs * Real.log (V₂ / V₁) = 0) :
    idealGasP m Rs T₂ V₂ / idealGasP m Rs T₁ V₁ = (V₁ / V₂) ^ γ := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have hCv : m * cv ≠ 0 := mul_ne_zero hm' hcv
  have hγ' : γ - 1 = m * Rs / (m * cv) := by
    rw [hγ]
    field_simp
  have had' : (m * cv) * Real.log (T₂ / T₁) + (m * Rs) * Real.log (V₂ / V₁) = 0 := by
    linear_combination m * had
  exact idealGasP_ratio_of_log_relation m Rs T₁ T₂ V₁ V₂ (m * cv) (m * Rs) γ
    hm hRs hT₁ hT₂ hV₁ hV₂ hCv hγ' had'

/-! ## D. Variable heat capacity -/

/-- Engineering energy balance with variable heat capacity: if `U` has temperature derivative
`Cv T` between `T₁` and `T₂` with `Cv` interval-integrable (the hypotheses of `kirchhoff_law`)
and the energy change obeys the IUPAC first law `U T₂ - U T₁ = q + w`, then
`Q_in - W_out = q - workOut w = ∫ T in T₁..T₂, Cv T`. The temperatures may be in either order.
The constant-`Cv` case is `heat_sub_workOut_eq`. -/
lemma heat_sub_workOut_eq_integral (U Cv : ℝ → ℝ) (T₁ T₂ q w : ℝ)
    (hU : ∀ T ∈ Set.uIcc T₁ T₂, HasDerivAt U (Cv T) T)
    (hCv : IntervalIntegrable Cv MeasureTheory.volume T₁ T₂)
    (hlaw : U T₂ - U T₁ = q + w) :
    q - workOut w = ∫ T in T₁..T₂, Cv T := by
  have h := kirchhoff_law U Cv T₁ T₂ hU hCv
  unfold workOut
  linarith

/-- Positive continuous heat capacity: if `U' = Cv` on `[T₁, T₂]` with `Cv` continuous and
positive there, then `U` is strictly increasing on `[T₁, T₂]` and
`ΔU = ∫ T in T₁..T₂, Cv T`; heating at positive heat capacity raises the internal energy. -/
lemma strictMonoOn_of_heatCapacity_pos (U Cv : ℝ → ℝ) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hU : ∀ T ∈ Set.Icc T₁ T₂, HasDerivAt U (Cv T) T)
    (hcont : ContinuousOn Cv (Set.Icc T₁ T₂)) (hpos : ∀ T ∈ Set.Icc T₁ T₂, 0 < Cv T) :
    StrictMonoOn U (Set.Icc T₁ T₂) ∧ U T₂ - U T₁ = ∫ T in T₁..T₂, Cv T := by
  have hcontU : ContinuousOn U (Set.Icc T₁ T₂) :=
    fun x hx => ((hU x hx).continuousAt).continuousWithinAt
  have hderiv : ∀ x ∈ interior (Set.Icc T₁ T₂), 0 < deriv U x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc T₁ T₂ := interior_subset hx
    rw [(hU x hxIcc).deriv]
    exact hpos x hxIcc
  refine ⟨strictMonoOn_of_deriv_pos (convex_Icc T₁ T₂) hcontU hderiv, ?_⟩
  have huIcc : Set.uIcc T₁ T₂ = Set.Icc T₁ T₂ := Set.uIcc_of_le hT
  have hU' : ∀ T ∈ Set.uIcc T₁ T₂, HasDerivAt U (Cv T) T := by
    rw [huIcc]
    exact hU
  have hCv : IntervalIntegrable Cv MeasureTheory.volume T₁ T₂ :=
    ContinuousOn.intervalIntegrable_of_Icc hT hcont
  have h := kirchhoff_law U Cv T₁ T₂ hU' hCv
  linarith

/-! ## E. Linear heat capacity versus the endpoint estimate -/

/-- The exact energy change for the linear heat capacity `Cv T = a + b * T`:
`∫ T in T₁..T₂, (a + b * T) = a * (T₂ - T₁) + b * (T₂ ^ 2 - T₁ ^ 2) / 2`. -/
lemma integral_linear_heatCapacity (a b T₁ T₂ : ℝ) :
    ∫ T in T₁..T₂, (a + b * T) = a * (T₂ - T₁) + b * (T₂ ^ 2 - T₁ ^ 2) / 2 := by
  have h1 : IntervalIntegrable (fun _ : ℝ => a) MeasureTheory.volume T₁ T₂ :=
    intervalIntegrable_const
  have h2 : IntervalIntegrable (fun T : ℝ => b * T) MeasureTheory.volume T₁ T₂ :=
    (continuous_id.const_mul b).intervalIntegrable T₁ T₂
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
  ring

/-- Endpoint error for the linear heat capacity: if `U' = a + b * T` at every temperature
between `T₁` and `T₂`, the exact change minus the endpoint estimate `Cv T₁ * (T₂ - T₁)` is the
signed amount `b * (T₂ - T₁) ^ 2 / 2`. For `T₁ ≠ T₂` its sign is that of `b`, for either
temperature order: the estimate is low when `Cv` rises with temperature and high when it falls.
At `T₁ = T₂` the error is zero and the estimate is exact. -/
lemma sub_sub_endpoint_of_linear_heatCapacity (U : ℝ → ℝ) (a b T₁ T₂ : ℝ)
    (hU : ∀ T ∈ Set.uIcc T₁ T₂, HasDerivAt U (a + b * T) T) :
    U T₂ - U T₁ - (a + b * T₁) * (T₂ - T₁) = b * (T₂ - T₁) ^ 2 / 2 := by
  have hCv : IntervalIntegrable (fun T : ℝ => a + b * T) MeasureTheory.volume T₁ T₂ :=
    (continuous_const.add (continuous_id.const_mul b)).intervalIntegrable T₁ T₂
  have h := kirchhoff_law U (fun T => a + b * T) T₁ T₂ hU hCv
  rw [integral_linear_heatCapacity] at h
  rw [h]
  ring

/-- A nonconstant linear heat capacity (`b ≠ 0`) over a nondegenerate interval (`T₁ ≠ T₂`):
the endpoint estimate `Cv T₁ * (T₂ - T₁)` is not the exact energy change. -/
lemma sub_ne_endpoint_of_linear_heatCapacity (U : ℝ → ℝ) {a b T₁ T₂ : ℝ}
    (hU : ∀ T ∈ Set.uIcc T₁ T₂, HasDerivAt U (a + b * T) T) (hb : b ≠ 0) (hT : T₁ ≠ T₂) :
    U T₂ - U T₁ ≠ (a + b * T₁) * (T₂ - T₁) := by
  have h := sub_sub_endpoint_of_linear_heatCapacity U a b T₁ T₂ hU
  have hsub : T₂ - T₁ ≠ 0 := by
    intro h0
    exact hT (sub_eq_zero.mp h0).symm
  have hsq : (T₂ - T₁) ^ 2 ≠ 0 := pow_ne_zero 2 hsub
  have hne : b * (T₂ - T₁) ^ 2 / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hb hsq) (by norm_num)
  intro hcon
  have h2 : b * (T₂ - T₁) ^ 2 / 2 = 0 := by rw [← h, hcon, sub_self]
  exact hne h2

end ProcessPorts
