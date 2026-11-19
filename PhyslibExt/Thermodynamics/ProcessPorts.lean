/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Thermodynamics.FirstLaw

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

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

Model inputs: the ideal-gas equation of state and the first law as encoded by the existing
declarations; temperatures are absolute (`T > 0`); volumes, amounts, masses and gas constants
are positive where a result says so. Each result assumes only the hypotheses its proof uses.
Celsius readings are affine and are never valid temperatures inside ratios or logarithms.

## ii. Key results

- `ProcessPorts.firstLaw_iff_workOut`: `ΔU = q + w ↔ ΔU = q - workOut w`.
- `ProcessPorts.workOut_isothermalWorkOn`: `∫ p dV = W_out = n R T log (V₂ / V₁)`.
- `ProcessPorts.workOut_irreversible_le_reversible`: `0 ≤ W_out,irr ≤ W_out,rev`.
- `ProcessPorts.idealGasP_ratio_of_specific_log_relation`: the adiabat with `k = m * Rs`.

## iii. Table of contents

- A. The work-out sign adapter
- B. Isothermal expansion work
- C. Molar and mass-specific coefficients

## iv. References

- E. R. Cohen et al., *Quantities, Units and Symbols in Physical Chemistry* (IUPAC Green Book),
  3rd ed., 2007: `ΔU = q + w` with `w` the work done on the system.
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 4:
  `ΔU = Q_in - W_out`, boundary work `W_b = m R T ln (V₂ / V₁)` of an isothermal ideal gas.
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

end ProcessPorts
