/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PhyslibExt.Chemistry.Thermodynamics.FirstLaw

/-!
# Gas cycles: refrigeration and power cycles

## i. Overview

Engineering cycle results, one section per device. Temperatures are absolute (`T > 0`); heats
and works are per cycle, and the first law over the cycle (`ΔU = 0`) relates them. The physics
inputs are hypotheses or existing results, never derived here: the Clausius inequality (the
second-law input, as in `PhyslibExt.Chemistry.Thermodynamics.Entropy`), the reversible
ideal-gas adiabat of `PhyslibExt.Chemistry.Thermodynamics.FirstLaw`, and the ideal-gas law
`p * V = nR * T` on the isobaric leg of the Diesel cycle.

Refrigerators and heat pumps (section A). A cycle absorbs `Qc` from a cold reservoir at `Tc`,
rejects `Qh` to a hot one at `Th` (`0 < Tc < Th`) and takes the work input `W = Qh - Qc`, the
work done on the working fluid (the engineering `W_out` of `PhyslibExt.Thermodynamics.ProcessPorts`
is `-W`). The refrigerator Clausius inequality reads `0 ≤ Qh / Th - Qc / Tc`. The coefficients of
performance `COP_R = Qc / W` and `COP_HP = Qh / W` are ratios of heat to work, not heat-engine
efficiencies, and can exceed one. With `W > 0` the Clausius inequality bounds them by the
reversible values `Tc / (Th - Tc)` and `Th / (Th - Tc)`, with equality exactly at zero Clausius
residual. Pumping heat `Qc > 0` uphill forces `W > 0`, and at `Th = Tc` no finite bound exists.

Ideal Otto cycle (section B). An ideal gas with constant total heat capacity `Cv > 0` and
`γ - 1 = nR / Cv` (`nR` the gas's `n * R`, or `m * Rs` with `Cv = m * cv`; one convention
throughout) starts at `(T₁, V₁)` with compression ratio `r = V₁ / V₂ > 1`. The states are
explicit: reversible adiabatic compression to `V₁ / r` at `T₂ = T₁ * r ^ (γ - 1)`, isochoric heat
input `Qin` to `T₃ = T₂ + Qin / Cv`, reversible adiabatic expansion back to `V₁` at
`T₄ = T₃ * r ^ (1 - γ)`, and isochoric rejection `Qout = Cv * (T₄ - T₁)`. Both adiabatic legs
satisfy the integrated adiabatic relation of the first-law module and so lie on its
`T * V ^ (γ - 1)` adiabat (`adiabatic_invariant_TV`); no further adiabat is introduced. The two
adiabats share the volume ratio `r`, so `Qout = r ^ (1 - γ) * Qin`, the net work output
(engineering sign) is `Wnet = Qin - Qout > 0`, and the efficiency is `Wnet / Qin = 1 - r ^ (1 - γ)`.
With zero heat input the loop does no work and the ratio is undefined.

Ideal Diesel cycle (section C). The same gas, with `Cp = γ * Cv = Cv + nR`, starts at
`(T₁, V₁)` with compression ratio `r` and cutoff ratio `rc = V₃ / V₂`, `1 < rc < r`. The
compression leg is the Otto one; heat is added at constant pressure `p₂ = nR * T₂ / V₂` up to the
cutoff volume `V₃ = rc * V₂`, where the ideal-gas law gives `T₃ = rc * T₂` and the first law on
the leg gives the heat input `Qin = Cv * (T₃ - T₂) + p₂ * (V₃ - V₂) = γ * Cv * (T₃ - T₂)`; the
reversible adiabatic expansion from `V₃` back to `V₁` lies on the same `T * V ^ (γ - 1)` adiabat
and ends at `T₄ = T₁ * rc ^ γ`; the closing isochoric leg rejects `Qout = Cv * (T₄ - T₁)`. The net
work output is `Wnet = Qin - Qout > 0`, the efficiency is
`Wnet / Qin = 1 - r ^ (1 - γ) * (rc ^ γ - 1) / (γ * (rc - 1))`, and the strict Bernoulli
inequality `rc ^ γ > 1 + γ * (rc - 1)` puts it strictly below the Otto efficiency at the same
compression ratio. The cutoff ratio `rc = 1` (no heat addition) is a limit of the formula, which
is the undefined `0 / 0` there, and a cutoff above `r` overshoots `V₁` and is not this cycle.

## ii. Key results

- `GasCycles.work_pos_of_clausius`: pumping heat `Qc > 0` uphill needs `W > 0`.
- `GasCycles.cop_le_carnot`: `Qc / W ≤ Tc / (Th - Tc)` and `Qh / W ≤ Th / (Th - Tc)`.
- `GasCycles.cop_eq_carnot_iff`: equality exactly at zero Clausius residual.
- `GasCycles.cop_unbounded_of_eq`: equal reservoir temperatures admit no finite bound.
- `GasCycles.ottoCompression_adiabat`, `GasCycles.ottoExpansion_adiabat`: both Otto legs lie on
  the existing adiabat.
- `GasCycles.otto_closed_loop`: `Qout = r ^ (1 - γ) * Qin` and `Wnet = Qin - Qout`.
- `GasCycles.ottoNetWork_div_heatIn`: `Wnet / Qin = ottoEfficiency r γ = 1 - r ^ (1 - γ)`.
- `GasCycles.otto_cycle`: the closed-state loop under the cycle's hypotheses.
- `GasCycles.dieselIsobaric_eos`: the ideal-gas law fixes the Diesel cutoff state and the heat
  input.
- `GasCycles.dieselExpansion_adiabat`: the Diesel expansion leg lies on the existing adiabat.
- `GasCycles.diesel_closed_loop`: `T₄ = T₁ * rc ^ γ` and `Wnet = Qin - Qout`.
- `GasCycles.dieselNetWork_div_heatIn`: `Wnet / Qin = dieselEfficiency r γ rc`.
- `GasCycles.dieselEfficiency_lt_ottoEfficiency`: the Diesel cycle is less efficient than the
  Otto cycle at the same compression ratio.
- `GasCycles.diesel_cycle`: the Diesel closed-state loop under the cycle's hypotheses.
- `GasCycles.dieselEfficiency_tendsto_ottoEfficiency`: the Otto efficiency is the limit
  `rc → 1`.

## iii. Table of contents

- A. Coefficients of performance and their second-law bounds
- B. Ideal Otto cycle
- C. Ideal Diesel cycle

## iv. References

- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 6:
  `COP_R = Q_L / W_net,in`, `COP_HP = Q_H / W_net,in`, the reversible values
  `1 / (T_H / T_L - 1)` and `1 / (1 - T_L / T_H)`, and the Clausius statement.
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 9:
  the ideal Otto cycle, `η = 1 - 1 / r ^ (k - 1)` under cold-air-standard assumptions.
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 9:
  the ideal Diesel cycle, cutoff ratio `rc = v₃ / v₂`,
  `η = 1 - (rc ^ k - 1) / (r ^ (k - 1) * k * (rc - 1))`, and `η_Otto > η_Diesel` at the same
  compression ratio, under cold-air-standard assumptions.
- MIT OpenCourseWare, 5.60 *Thermodynamics & Kinetics* (Spring 2008): the Clausius inequality.
- P. Atkins and J. de Paula, *Atkins' Physical Chemistry*, Chapter 2: reversible adiabatic change
  of a perfect gas, `T V ^ (γ - 1)` constant.
-/

@[expose] public section

namespace GasCycles

/-! ## A. Coefficients of performance and their second-law bounds -/

/-- Pumping heat uphill needs work (the Clausius statement): between reservoirs at
`0 < Tc < Th`, a cycle that absorbs `Qc > 0` at `Tc`, rejects `Qh` at `Th` and satisfies the
refrigerator Clausius inequality `0 ≤ Qh / Th - Qc / Tc` has work input `W = Qh - Qc > 0`. -/
lemma work_pos_of_clausius {Qh Qc W Tc Th : ℝ} (hTc : 0 < Tc) (hT : Tc < Th) (hQc : 0 < Qc)
    (hW : W = Qh - Qc) (hClausius : 0 ≤ Qh / Th - Qc / Tc) :
    0 < W := by
  have hTh : 0 < Th := lt_trans hTc hT
  have h1 : Qc / Tc ≤ Qh / Th := by linarith
  have h2 : Qc * Th ≤ Qh * Tc := (div_le_div_iff₀ hTc hTh).mp h1
  have h3 : Qc * Tc < Qc * Th := mul_lt_mul_of_pos_left hT hQc
  have h4 : Qc * Tc < Qh * Tc := lt_of_lt_of_le h3 h2
  have h5 : Qc < Qh := by
    by_contra hcon
    have hle : Qh ≤ Qc := le_of_not_gt hcon
    have h6 : Qh * Tc ≤ Qc * Tc := mul_le_mul_of_nonneg_right hle (le_of_lt hTc)
    linarith
  linarith

/-- Second-law bounds on the coefficients of performance: between reservoirs at `0 < Tc < Th`,
with work input `W = Qh - Qc > 0` and the refrigerator Clausius inequality
`0 ≤ Qh / Th - Qc / Tc`, the refrigerator `COP_R = Qc / W` is at most `Tc / (Th - Tc)` and the
heat pump `COP_HP = Qh / W` is at most `Th / (Th - Tc)`. -/
lemma cop_le_carnot {Qh Qc W Tc Th : ℝ} (hTc : 0 < Tc) (hT : Tc < Th) (hW : W = Qh - Qc)
    (hWpos : 0 < W) (hClausius : 0 ≤ Qh / Th - Qc / Tc) :
    Qc / W ≤ Tc / (Th - Tc) ∧ Qh / W ≤ Th / (Th - Tc) := by
  have hTh : 0 < Th := lt_trans hTc hT
  have hD : 0 < Th - Tc := sub_pos.mpr hT
  have h2 : Qc * Th ≤ Qh * Tc := (div_le_div_iff₀ hTc hTh).mp (by linarith)
  constructor
  · rw [div_le_div_iff₀ hWpos hD, hW]
    linarith
  · rw [div_le_div_iff₀ hWpos hD, hW]
    linarith

/-- Equality exactly at zero Clausius residual: with `0 < Tc < Th` and `W = Qh - Qc > 0`,
`COP_R = Tc / (Th - Tc)` holds if and only if `Qh / Th - Qc / Tc = 0`, and likewise
`COP_HP = Th / (Th - Tc)`. The Clausius inequality is not needed for the equivalence. -/
lemma cop_eq_carnot_iff {Qh Qc W Tc Th : ℝ} (hTc : 0 < Tc) (hT : Tc < Th) (hW : W = Qh - Qc)
    (hWpos : 0 < W) :
    (Qc / W = Tc / (Th - Tc) ↔ Qh / Th - Qc / Tc = 0) ∧
      (Qh / W = Th / (Th - Tc) ↔ Qh / Th - Qc / Tc = 0) := by
  have hTh : 0 < Th := lt_trans hTc hT
  have hD : 0 < Th - Tc := sub_pos.mpr hT
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hDne : Th - Tc ≠ 0 := ne_of_gt hD
  have hTcne : Tc ≠ 0 := ne_of_gt hTc
  have hThne : Th ≠ 0 := ne_of_gt hTh
  have hres : Qh / Th - Qc / Tc = 0 ↔ Qc * Th = Qh * Tc := by
    rw [sub_eq_zero, div_eq_div_iff hThne hTcne]
    exact eq_comm
  constructor
  · rw [div_eq_div_iff hWne hDne, hW, hres]
    constructor <;> intro h <;> linarith
  · rw [div_eq_div_iff hWne hDne, hW, hres]
    constructor <;> intro h <;> linarith

/-- Equal reservoir temperatures admit no finite bound: at `Th = Tc = T > 0`, for every `M`
there are heats and work with `Qc > 0`, `W = Qh - Qc > 0` and the Clausius inequality whose
`COP_R` and `COP_HP` both exceed `M`. The hypothesis `Tc < Th` of `cop_le_carnot` cannot be
weakened to `Tc ≤ Th`. -/
lemma cop_unbounded_of_eq {T : ℝ} (hT : 0 < T) (M : ℝ) :
    ∃ Qh Qc W : ℝ, 0 < Qc ∧ W = Qh - Qc ∧ 0 < W ∧ 0 ≤ Qh / T - Qc / T ∧
      M < Qc / W ∧ M < Qh / W := by
  refine ⟨|M| + 2, |M| + 1, 1, by positivity, by ring, by norm_num, ?_, ?_, ?_⟩
  · have h : (|M| + 2) / T - (|M| + 1) / T = 1 / T := by
      rw [← sub_div]
      congr 1
      ring
    rw [h]
    exact le_of_lt (div_pos one_pos hT)
  · rw [div_one]
    have hM := le_abs_self M
    linarith
  · rw [div_one]
    have hM := le_abs_self M
    linarith

/-! ## B. Ideal Otto cycle -/

open Chemistry.Thermodynamics

/-- Ideal Otto efficiency `1 - r ^ (1 - γ)` at compression ratio `r = V₁ / V₂` and
heat-capacity ratio `γ`. Physical domain `r > 1`, `γ > 1`, where the value lies strictly between
`0` and `1`. -/
noncomputable def ottoEfficiency (r γ : ℝ) : ℝ := 1 - r ^ (1 - γ)

/-- Temperature after the reversible adiabatic compression from `(T₁, V₁)` to volume `V₁ / r`:
`T₂ = T₁ * r ^ (γ - 1)`. -/
noncomputable def ottoCompressedTemp (T₁ r γ : ℝ) : ℝ := T₁ * r ^ (γ - 1)

/-- Peak temperature after the isochoric heat input `Qin` at total heat capacity `Cv`:
`T₃ = T₂ + Qin / Cv`. -/
noncomputable def ottoPeakTemp (T₁ r γ Cv Qin : ℝ) : ℝ := ottoCompressedTemp T₁ r γ + Qin / Cv

/-- Temperature after the reversible adiabatic expansion from `(T₃, V₁ / r)` back to `V₁`:
`T₄ = T₃ * r ^ (1 - γ)`. -/
noncomputable def ottoExpandedTemp (T₁ r γ Cv Qin : ℝ) : ℝ :=
  ottoPeakTemp T₁ r γ Cv Qin * r ^ (1 - γ)

/-- Heat rejected on the closing isochoric leg `4 → 1`: `Qout = Cv * (T₄ - T₁)`. -/
noncomputable def ottoHeatOut (T₁ r γ Cv Qin : ℝ) : ℝ :=
  Cv * (ottoExpandedTemp T₁ r γ Cv Qin - T₁)

/-- Net work output of the loop (engineering `W_out`, from `W_out = -ΔU` on each adiabatic leg
and no work on the isochoric legs): expansion work `Cv * (T₃ - T₄)` minus compression work
`Cv * (T₂ - T₁)`. -/
noncomputable def ottoNetWork (T₁ r γ Cv Qin : ℝ) : ℝ :=
  Cv * (ottoPeakTemp T₁ r γ Cv Qin - ottoExpandedTemp T₁ r γ Cv Qin) -
    Cv * (ottoCompressedTemp T₁ r γ - T₁)

/-- Compression leg on the existing adiabat: for `0 < T₁`, `0 < V₁`, `0 < r`, `Cv ≠ 0` and
`γ - 1 = nR / Cv`, the states `(T₁, V₁)` and `(T₂, V₁ / r)` satisfy the integrated adiabatic
relation `Cv * log (T₂ / T₁) + nR * log (V₂ / V₁) = 0`, hence the invariant
`T₂ * V₂ ^ (γ - 1) = T₁ * V₁ ^ (γ - 1)` of `adiabatic_invariant_TV`. -/
lemma ottoCompression_adiabat {T₁ V₁ r γ Cv nR : ℝ} (hT₁ : 0 < T₁) (hV₁ : 0 < V₁)
    (hr : 0 < r) (hCv : Cv ≠ 0) (hγ : γ - 1 = nR / Cv) :
    Cv * Real.log (ottoCompressedTemp T₁ r γ / T₁) + nR * Real.log (V₁ / r / V₁) = 0 ∧
      ottoCompressedTemp T₁ r γ * (V₁ / r) ^ (γ - 1) = T₁ * V₁ ^ (γ - 1) := by
  have hT₁' : T₁ ≠ 0 := ne_of_gt hT₁
  have hV₁' : V₁ ≠ 0 := ne_of_gt hV₁
  have hr' : r ≠ 0 := ne_of_gt hr
  have hVpos : 0 < V₁ / r := div_pos hV₁ hr
  have hpow_pos : 0 < r ^ (γ - 1) := Real.rpow_pos_of_pos hr _
  have hT₂ : 0 < ottoCompressedTemp T₁ r γ := by
    simp only [ottoCompressedTemp]
    exact mul_pos hT₁ hpow_pos
  have hTdiv : ottoCompressedTemp T₁ r γ / T₁ = r ^ (γ - 1) := by
    simp only [ottoCompressedTemp]
    field_simp
  have hVdiv : V₁ / r / V₁ = r⁻¹ := by
    field_simp
  have hlogT : Real.log (ottoCompressedTemp T₁ r γ / T₁) = (γ - 1) * Real.log r := by
    rw [hTdiv, Real.log_rpow hr]
  have hlogV : Real.log (V₁ / r / V₁) = -Real.log r := by
    rw [hVdiv, Real.log_inv]
  have hCv_eq : Cv * (γ - 1) = nR := by
    rw [hγ]
    field_simp
  have had : Cv * Real.log (ottoCompressedTemp T₁ r γ / T₁)
      + nR * Real.log (V₁ / r / V₁) = 0 := by
    rw [hlogT, hlogV]
    linear_combination Real.log r * hCv_eq
  refine ⟨had, ?_⟩
  exact adiabatic_invariant_TV T₁ (ottoCompressedTemp T₁ r γ) V₁ (V₁ / r) Cv nR γ
    hT₁ hT₂ hV₁ hVpos hCv hγ had

/-- Expansion leg on the existing adiabat: with also `0 < Cv` and `0 ≤ Qin` (so `T₃ > 0`), the
states `(T₃, V₁ / r)` and `(T₄, V₁)` satisfy the integrated adiabatic relation, hence
`T₄ * V₁ ^ (γ - 1) = T₃ * (V₁ / r) ^ (γ - 1)`. -/
lemma ottoExpansion_adiabat {T₁ V₁ r γ Cv nR Qin : ℝ} (hT₁ : 0 < T₁) (hV₁ : 0 < V₁)
    (hr : 0 < r) (hCv : 0 < Cv) (hQin : 0 ≤ Qin) (hγ : γ - 1 = nR / Cv) :
    Cv * Real.log (ottoExpandedTemp T₁ r γ Cv Qin / ottoPeakTemp T₁ r γ Cv Qin) +
        nR * Real.log (V₁ / (V₁ / r)) = 0 ∧
      ottoExpandedTemp T₁ r γ Cv Qin * V₁ ^ (γ - 1) =
        ottoPeakTemp T₁ r γ Cv Qin * (V₁ / r) ^ (γ - 1) := by
  have hV₁' : V₁ ≠ 0 := ne_of_gt hV₁
  have hr' : r ≠ 0 := ne_of_gt hr
  have hCv' : Cv ≠ 0 := ne_of_gt hCv
  have hVpos : 0 < V₁ / r := div_pos hV₁ hr
  have hpow_comp : 0 < r ^ (γ - 1) := Real.rpow_pos_of_pos hr _
  have hT₂ : 0 < ottoCompressedTemp T₁ r γ := by
    simp only [ottoCompressedTemp]
    exact mul_pos hT₁ hpow_comp
  have hQdiv_nonneg : 0 ≤ Qin / Cv := div_nonneg hQin (le_of_lt hCv)
  have hpeak_pos : 0 < ottoPeakTemp T₁ r γ Cv Qin := by
    simp only [ottoPeakTemp]
    linarith
  have hpow_exp : 0 < r ^ (1 - γ) := Real.rpow_pos_of_pos hr _
  have hexp_pos : 0 < ottoExpandedTemp T₁ r γ Cv Qin := by
    simp only [ottoExpandedTemp]
    exact mul_pos hpeak_pos hpow_exp
  have hTdiv : ottoExpandedTemp T₁ r γ Cv Qin / ottoPeakTemp T₁ r γ Cv Qin
      = r ^ (1 - γ) := by
    simp only [ottoExpandedTemp]
    field_simp
  have hVdiv : V₁ / (V₁ / r) = r := by
    field_simp
  have hlogT : Real.log (ottoExpandedTemp T₁ r γ Cv Qin / ottoPeakTemp T₁ r γ Cv Qin)
      = (1 - γ) * Real.log r := by
    rw [hTdiv, Real.log_rpow hr]
  have hlogV : Real.log (V₁ / (V₁ / r)) = Real.log r := by
    rw [hVdiv]
  have hCv_eq : Cv * (γ - 1) = nR := by
    rw [hγ]
    field_simp
  have hCv_eq2 : Cv * (1 - γ) = -nR := by
    linear_combination -hCv_eq
  have had : Cv * Real.log (ottoExpandedTemp T₁ r γ Cv Qin / ottoPeakTemp T₁ r γ Cv Qin)
      + nR * Real.log (V₁ / (V₁ / r)) = 0 := by
    rw [hlogT, hlogV]
    linear_combination Real.log r * hCv_eq2
  refine ⟨had, ?_⟩
  exact adiabatic_invariant_TV (ottoPeakTemp T₁ r γ Cv Qin)
    (ottoExpandedTemp T₁ r γ Cv Qin) (V₁ / r) V₁ Cv nR γ
    hpeak_pos hexp_pos hVpos hV₁ hCv' hγ had

/-- The loop closes: for `0 < r` and `Cv ≠ 0`, the heat-input leg absorbs
`Cv * (T₃ - T₂) = Qin`; the closing isochoric leg rejects `Qout = r ^ (1 - γ) * Qin`, because
both adiabats have the volume ratio `r`; and the net work is the net heat, `Wnet = Qin - Qout`. -/
lemma otto_closed_loop {T₁ r γ Cv Qin : ℝ} (hr : 0 < r) (hCv : Cv ≠ 0) :
    Cv * (ottoPeakTemp T₁ r γ Cv Qin - ottoCompressedTemp T₁ r γ) = Qin ∧
      ottoHeatOut T₁ r γ Cv Qin = r ^ (1 - γ) * Qin ∧
      ottoNetWork T₁ r γ Cv Qin = Qin - ottoHeatOut T₁ r γ Cv Qin := by
  have h1 : Cv * (ottoPeakTemp T₁ r γ Cv Qin - ottoCompressedTemp T₁ r γ) = Qin := by
    simp only [ottoPeakTemp]
    field_simp
    ring
  have hpow : r ^ (γ - 1) * r ^ (1 - γ) = 1 := by
    rw [← Real.rpow_add hr]
    have hexp : (γ - 1) + (1 - γ) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  have h2 : ottoHeatOut T₁ r γ Cv Qin = r ^ (1 - γ) * Qin := by
    simp only [ottoHeatOut, ottoExpandedTemp, ottoPeakTemp, ottoCompressedTemp]
    have hmul : T₁ * r ^ (γ - 1) * r ^ (1 - γ) = T₁ := by
      calc T₁ * r ^ (γ - 1) * r ^ (1 - γ)
          = T₁ * (r ^ (γ - 1) * r ^ (1 - γ)) := by ring
        _ = T₁ * 1 := by rw [hpow]
        _ = T₁ := by ring
    have hexpand : (T₁ * r ^ (γ - 1) + Qin / Cv) * r ^ (1 - γ)
        = T₁ + Qin / Cv * r ^ (1 - γ) := by
      calc (T₁ * r ^ (γ - 1) + Qin / Cv) * r ^ (1 - γ)
          = T₁ * r ^ (γ - 1) * r ^ (1 - γ) + Qin / Cv * r ^ (1 - γ) := by ring
        _ = T₁ + Qin / Cv * r ^ (1 - γ) := by rw [hmul]
    rw [hexpand]
    field_simp
    ring
  have h3 : ottoNetWork T₁ r γ Cv Qin = Qin - ottoHeatOut T₁ r γ Cv Qin := by
    simp only [ottoNetWork, ottoHeatOut]
    linear_combination h1
  exact ⟨h1, h2, h3⟩

/-- Nondegenerate loop: for `r > 1`, `γ > 1`, `Cv ≠ 0` and `Qin > 0`, the rejected heat and the
net work are both positive. -/
lemma otto_heatOut_pos_netWork_pos {T₁ r γ Cv Qin : ℝ} (hr : 1 < r) (hγ : 1 < γ)
    (hCv : Cv ≠ 0) (hQin : 0 < Qin) :
    0 < ottoHeatOut T₁ r γ Cv Qin ∧ 0 < ottoNetWork T₁ r γ Cv Qin := by
  have h0r : 0 < r := by linarith
  obtain ⟨_, hQout, hWnet⟩ := @otto_closed_loop T₁ r γ Cv Qin h0r hCv
  have hexp_neg : 1 - γ < 0 := by linarith
  have hpow_pos : 0 < r ^ (1 - γ) := Real.rpow_pos_of_pos h0r _
  have hpow_lt_one : r ^ (1 - γ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hr hexp_neg
  have hHeat_pos : 0 < ottoHeatOut T₁ r γ Cv Qin := by
    rw [hQout]
    exact mul_pos hpow_pos hQin
  have hlt : r ^ (1 - γ) * Qin < Qin := by
    calc r ^ (1 - γ) * Qin < 1 * Qin := mul_lt_mul_of_pos_right hpow_lt_one hQin
      _ = Qin := one_mul Qin
  have hWork_pos : 0 < ottoNetWork T₁ r γ Cv Qin := by
    rw [hWnet, hQout, sub_pos]
    exact hlt
  exact ⟨hHeat_pos, hWork_pos⟩

/-- Otto efficiency: for `0 < r`, `Cv ≠ 0` and nonzero heat input, the work-to-heat ratio of the
loop is `Wnet / Qin = 1 - r ^ (1 - γ) = ottoEfficiency r γ`, and so is `1 - Qout / Qin`. -/
lemma ottoNetWork_div_heatIn {T₁ r γ Cv Qin : ℝ} (hr : 0 < r) (hCv : Cv ≠ 0)
    (hQin : Qin ≠ 0) :
    ottoNetWork T₁ r γ Cv Qin / Qin = ottoEfficiency r γ ∧
      1 - ottoHeatOut T₁ r γ Cv Qin / Qin = ottoEfficiency r γ := by
  obtain ⟨_, hQout, hWnet⟩ := @otto_closed_loop T₁ r γ Cv Qin hr hCv
  have hW : ottoNetWork T₁ r γ Cv Qin = Qin - r ^ (1 - γ) * Qin := by
    rw [hWnet, hQout]
  refine ⟨?_, ?_⟩
  · simp only [ottoEfficiency]
    rw [hW]
    field_simp
  · simp only [ottoEfficiency]
    rw [hQout]
    field_simp

/-- The ideal Otto closed-state loop: for `r > 1`, `γ > 1` with `γ - 1 = nR / Cv`, constant
`Cv > 0`, `T₁ > 0`, `V₁ > 0` and positive isochoric heat input `Qin`, the states
`(T₁, V₁) → (T₂, V₁ / r) → (T₃, V₁ / r) → (T₄, V₁) → (T₁, V₁)` have both adiabatic legs on the
`T * V ^ (γ - 1)` adiabat, the net work `Wnet = Qin - Qout` and the rejected heat are positive,
and the efficiency is `Wnet / Qin = 1 - r ^ (1 - γ)`. -/
lemma otto_cycle {T₁ V₁ r γ Cv nR Qin : ℝ} (hT₁ : 0 < T₁) (hV₁ : 0 < V₁) (hr : 1 < r)
    (hγ₁ : 1 < γ) (hCv : 0 < Cv) (hγ : γ - 1 = nR / Cv) (hQin : 0 < Qin) :
    ottoCompressedTemp T₁ r γ * (V₁ / r) ^ (γ - 1) = T₁ * V₁ ^ (γ - 1) ∧
      ottoExpandedTemp T₁ r γ Cv Qin * V₁ ^ (γ - 1) =
        ottoPeakTemp T₁ r γ Cv Qin * (V₁ / r) ^ (γ - 1) ∧
      ottoNetWork T₁ r γ Cv Qin = Qin - ottoHeatOut T₁ r γ Cv Qin ∧
      0 < ottoHeatOut T₁ r γ Cv Qin ∧ 0 < ottoNetWork T₁ r γ Cv Qin ∧
      ottoNetWork T₁ r γ Cv Qin / Qin = 1 - r ^ (1 - γ) := by
  have h0r : 0 < r := by linarith
  have hCv' : Cv ≠ 0 := ne_of_gt hCv
  have hQin0 : Qin ≠ 0 := ne_of_gt hQin
  have hQin_nonneg : 0 ≤ Qin := le_of_lt hQin
  obtain ⟨_, hcomp⟩ := @ottoCompression_adiabat T₁ V₁ r γ Cv nR hT₁ hV₁ h0r hCv' hγ
  obtain ⟨_, hexp⟩ := @ottoExpansion_adiabat T₁ V₁ r γ Cv nR Qin hT₁ hV₁ h0r hCv hQin_nonneg hγ
  obtain ⟨_, _, hclose⟩ := @otto_closed_loop T₁ r γ Cv Qin h0r hCv'
  obtain ⟨hQpos, hWpos⟩ := @otto_heatOut_pos_netWork_pos T₁ r γ Cv Qin hr hγ₁ hCv' hQin
  obtain ⟨hdiv, _⟩ := @ottoNetWork_div_heatIn T₁ r γ Cv Qin h0r hCv' hQin0
  have hdiv' : ottoNetWork T₁ r γ Cv Qin / Qin = 1 - r ^ (1 - γ) := by
    simpa [ottoEfficiency] using hdiv
  exact ⟨hcomp, hexp, hclose, hQpos, hWpos, hdiv'⟩

/-- Zero heat input: with `Qin = 0` the loop does no net work, so its efficiency as a work/heat
ratio is the undefined `0 / 0`. Lean's value for it, `0`, is not `ottoEfficiency r γ` when
`r > 1` and `γ > 1`. -/
lemma otto_zero_heatIn {T₁ r γ Cv : ℝ} (hr : 1 < r) (hγ : 1 < γ) :
    ottoNetWork T₁ r γ Cv 0 = 0 ∧ ottoNetWork T₁ r γ Cv 0 / 0 ≠ ottoEfficiency r γ := by
  have h0r : 0 < r := by linarith
  have hpow : r ^ (γ - 1) * r ^ (1 - γ) = 1 := by
    rw [← Real.rpow_add h0r]
    have hexp : (γ - 1) + (1 - γ) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  have hpeak : ottoPeakTemp T₁ r γ Cv 0 = ottoCompressedTemp T₁ r γ := by
    simp [ottoPeakTemp]
  have hexp : ottoExpandedTemp T₁ r γ Cv 0 = T₁ := by
    simp only [ottoExpandedTemp, hpeak, ottoCompressedTemp]
    calc T₁ * r ^ (γ - 1) * r ^ (1 - γ)
        = T₁ * (r ^ (γ - 1) * r ^ (1 - γ)) := by ring
      _ = T₁ * 1 := by rw [hpow]
      _ = T₁ := by ring
  have hW0 : ottoNetWork T₁ r γ Cv 0 = 0 := by
    simp only [ottoNetWork, hpeak, hexp, sub_self]
  have hexp_neg : 1 - γ < 0 := by linarith
  have hpow_lt_one : r ^ (1 - γ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hr hexp_neg
  have heff_pos : 0 < ottoEfficiency r γ := by
    simp only [ottoEfficiency]
    linarith
  have hne : (ottoNetWork T₁ r γ Cv 0 / 0) ≠ ottoEfficiency r γ := by
    rw [hW0, zero_div]
    exact ne_of_lt heff_pos
  exact ⟨hW0, hne⟩

/-! ## C. Ideal Diesel cycle -/

/-! ### States, heats and work -/

/-- Ideal Diesel efficiency at compression ratio `r = V₁ / V₂`, cutoff ratio `rc = V₃ / V₂` and
heat-capacity ratio `γ`: `1 - r ^ (1 - γ) * (rc ^ γ - 1) / (γ * (rc - 1))`. Physical domain
`1 < rc < r`, `γ > 1`. At `rc = 1` the quotient is the undefined `0 / 0`; the Otto value there
is a limit (`dieselEfficiency_tendsto_ottoEfficiency`), not a value of this formula. -/
noncomputable def dieselEfficiency (r γ rc : ℝ) : ℝ :=
  1 - r ^ (1 - γ) * (rc ^ γ - 1) / (γ * (rc - 1))

/-- Temperature at the end of the isobaric heat addition, the cutoff state at volume
`V₃ = rc * V₂`: `T₃ = rc * T₂`, the ideal-gas law at constant pressure (`dieselIsobaric_eos`). -/
noncomputable def dieselCutoffTemp (T₁ r γ rc : ℝ) : ℝ := rc * ottoCompressedTemp T₁ r γ

/-- Temperature after the reversible adiabatic expansion from the cutoff state
`(T₃, rc * (V₁ / r))` back to `V₁`: `T₄ = T₃ * (rc / r) ^ (γ - 1)`. -/
noncomputable def dieselExpandedTemp (T₁ r γ rc : ℝ) : ℝ :=
  dieselCutoffTemp T₁ r γ rc * (rc / r) ^ (γ - 1)

/-- Heat input on the isobaric leg `2 → 3`: `Qin = Cp * (T₃ - T₂)` with `Cp = γ * Cv`, which is
`Cv + nR` for this gas. -/
noncomputable def dieselHeatIn (T₁ r γ Cv rc : ℝ) : ℝ :=
  γ * Cv * (dieselCutoffTemp T₁ r γ rc - ottoCompressedTemp T₁ r γ)

/-- Heat rejected on the closing isochoric leg `4 → 1`: `Qout = Cv * (T₄ - T₁)`. -/
noncomputable def dieselHeatOut (T₁ r γ Cv rc : ℝ) : ℝ :=
  Cv * (dieselExpandedTemp T₁ r γ rc - T₁)

/-- Net work output of the loop (engineering `W_out`): the boundary work `p₂ * (V₃ - V₂)` of the
isobaric leg, which is `nR * (T₃ - T₂)` by the ideal-gas law, plus the expansion work
`Cv * (T₃ - T₄)` (`W_out = -ΔU` on an adiabatic leg), minus the compression work
`Cv * (T₂ - T₁)`; the closing isochoric leg does no work. -/
noncomputable def dieselNetWork (T₁ r γ Cv nR rc : ℝ) : ℝ :=
  nR * (dieselCutoffTemp T₁ r γ rc - ottoCompressedTemp T₁ r γ) +
    Cv * (dieselCutoffTemp T₁ r γ rc - dieselExpandedTemp T₁ r γ rc) -
    Cv * (ottoCompressedTemp T₁ r γ - T₁)

/-! ### The isobaric and expansion legs -/

/-- Isobaric heat addition under the ideal-gas law `p * V = nR * T`: if state `2`
(`V₂ = V₁ / r`, temperature `T₂`) and state `3` (`V₃ = rc * V₂`, temperature `T₃`) obey the law
at the same pressure `p`, then `T₃ = rc * T₂` is the cutoff temperature, and the first law on the
leg, `Q = Cv * (T₃ - T₂) + p * (V₃ - V₂)` (internal-energy change plus boundary work), gives the
heat input `Q = γ * Cv * (T₃ - T₂)`. -/
lemma dieselIsobaric_eos {T₁ V₁ r γ Cv nR rc p T₃ : ℝ} (hnR : nR ≠ 0) (hCv : Cv ≠ 0)
    (hγ : γ - 1 = nR / Cv) (h₂ : p * (V₁ / r) = nR * ottoCompressedTemp T₁ r γ)
    (h₃ : p * (rc * (V₁ / r)) = nR * T₃) :
    T₃ = dieselCutoffTemp T₁ r γ rc ∧
      Cv * (T₃ - ottoCompressedTemp T₁ r γ) + p * (rc * (V₁ / r) - V₁ / r) =
        dieselHeatIn T₁ r γ Cv rc := by
  have hV : p * (rc * (V₁ / r)) = rc * (p * (V₁ / r)) := by ring
  have hT : nR * T₃ = nR * (rc * ottoCompressedTemp T₁ r γ) := by
    calc nR * T₃ = p * (rc * (V₁ / r)) := h₃.symm
      _ = rc * (p * (V₁ / r)) := hV
      _ = rc * (nR * ottoCompressedTemp T₁ r γ) := by rw [h₂]
      _ = nR * (rc * ottoCompressedTemp T₁ r γ) := by ring
  have hTeq : T₃ = rc * ottoCompressedTemp T₁ r γ := mul_left_cancel₀ hnR hT
  have hfirst : T₃ = dieselCutoffTemp T₁ r γ rc := by
    simp only [dieselCutoffTemp]
    exact hTeq
  have hp : p * (rc * (V₁ / r) - V₁ / r) = nR * (T₃ - ottoCompressedTemp T₁ r γ) := by
    linear_combination h₃ - h₂
  have hCveq : Cv * (γ - 1) = nR := by
    rw [hγ]
    field_simp
  have hCp : γ * Cv = Cv + nR := by
    linear_combination hCveq
  refine ⟨hfirst, ?_⟩
  simp only [dieselHeatIn]
  rw [← hfirst, hp]
  linear_combination -(T₃ - ottoCompressedTemp T₁ r γ) * hCp

/-- Expansion leg on the existing adiabat: for `0 < T₁`, `0 < V₁`, `0 < r`, `0 < rc`, `Cv ≠ 0`
and `γ - 1 = nR / Cv`, the cutoff state `(T₃, V₃)` with `V₃ = rc * (V₁ / r)` and the state
`(T₄, V₁)` satisfy the integrated adiabatic relation
`Cv * log (T₄ / T₃) + nR * log (V₁ / V₃) = 0`, hence the invariant
`T₄ * V₁ ^ (γ - 1) = T₃ * V₃ ^ (γ - 1)` of `adiabatic_invariant_TV`. -/
lemma dieselExpansion_adiabat {T₁ V₁ r γ Cv nR rc : ℝ} (hT₁ : 0 < T₁) (hV₁ : 0 < V₁)
    (hr : 0 < r) (hrc : 0 < rc) (hCv : Cv ≠ 0) (hγ : γ - 1 = nR / Cv) :
    Cv * Real.log (dieselExpandedTemp T₁ r γ rc / dieselCutoffTemp T₁ r γ rc) +
        nR * Real.log (V₁ / (rc * (V₁ / r))) = 0 ∧
      dieselExpandedTemp T₁ r γ rc * V₁ ^ (γ - 1) =
        dieselCutoffTemp T₁ r γ rc * (rc * (V₁ / r)) ^ (γ - 1) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hrc' : rc ≠ 0 := ne_of_gt hrc
  have hV₁' : V₁ ≠ 0 := ne_of_gt hV₁
  have hrcr : 0 < rc / r := div_pos hrc hr
  have hpow1 : 0 < r ^ (γ - 1) := Real.rpow_pos_of_pos hr _
  have hT₃ : 0 < dieselCutoffTemp T₁ r γ rc := by
    simp only [dieselCutoffTemp, ottoCompressedTemp]
    exact mul_pos hrc (mul_pos hT₁ hpow1)
  have hpow2 : 0 < (rc / r) ^ (γ - 1) := Real.rpow_pos_of_pos hrcr _
  have hT₄ : 0 < dieselExpandedTemp T₁ r γ rc := by
    simp only [dieselExpandedTemp]
    exact mul_pos hT₃ hpow2
  have hV₃ : 0 < rc * (V₁ / r) := by positivity
  have hTdiv : dieselExpandedTemp T₁ r γ rc / dieselCutoffTemp T₁ r γ rc
      = (rc / r) ^ (γ - 1) := by
    simp only [dieselExpandedTemp]
    field_simp
  have hVdiv : V₁ / (rc * (V₁ / r)) = (rc / r)⁻¹ := by
    field_simp
  have hlogT : Real.log (dieselExpandedTemp T₁ r γ rc / dieselCutoffTemp T₁ r γ rc)
      = (γ - 1) * Real.log (rc / r) := by
    rw [hTdiv, Real.log_rpow hrcr]
  have hlogV : Real.log (V₁ / (rc * (V₁ / r))) = -Real.log (rc / r) := by
    rw [hVdiv, Real.log_inv]
  have hCveq : Cv * (γ - 1) = nR := by
    rw [hγ]
    field_simp
  have had : Cv * Real.log (dieselExpandedTemp T₁ r γ rc / dieselCutoffTemp T₁ r γ rc)
      + nR * Real.log (V₁ / (rc * (V₁ / r))) = 0 := by
    rw [hlogT, hlogV]
    linear_combination Real.log (rc / r) * hCveq
  refine ⟨had, ?_⟩
  exact adiabatic_invariant_TV (dieselCutoffTemp T₁ r γ rc)
    (dieselExpandedTemp T₁ r γ rc) (rc * (V₁ / r)) V₁ Cv nR γ
    hT₃ hT₄ hV₃ hV₁ hCv hγ had

/-! ### Closure, efficiency and the Otto comparison -/

/-- The loop closes: for `0 < r`, `0 < rc`, `Cv ≠ 0` and `γ - 1 = nR / Cv`, the expansion ends
at `T₄ = T₁ * rc ^ γ`, so the rejected heat is `Qout = Cv * T₁ * (rc ^ γ - 1)`; the heat input is
`Qin = γ * Cv * T₁ * r ^ (γ - 1) * (rc - 1)`; and the net work is the net heat,
`Wnet = Qin - Qout`. -/
lemma diesel_closed_loop {T₁ r γ Cv nR rc : ℝ} (hr : 0 < r) (hrc : 0 < rc) (hCv : Cv ≠ 0)
    (hγ : γ - 1 = nR / Cv) :
    dieselExpandedTemp T₁ r γ rc = T₁ * rc ^ γ ∧
      dieselHeatOut T₁ r γ Cv rc = Cv * T₁ * (rc ^ γ - 1) ∧
      dieselHeatIn T₁ r γ Cv rc = γ * Cv * T₁ * r ^ (γ - 1) * (rc - 1) ∧
      dieselNetWork T₁ r γ Cv nR rc =
        dieselHeatIn T₁ r γ Cv rc - dieselHeatOut T₁ r γ Cv rc := by
  have hrpow_ne : r ^ (γ - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr _)
  have hdiv : (rc / r) ^ (γ - 1) = rc ^ (γ - 1) / r ^ (γ - 1) :=
    Real.div_rpow (le_of_lt hrc) (le_of_lt hr) _
  have hrc_pow : rc * rc ^ (γ - 1) = rc ^ γ := by
    have h1 : (1 : ℝ) + (γ - 1) = γ := by ring
    have h2 := Real.rpow_add hrc 1 (γ - 1)
    rw [h1, Real.rpow_one] at h2
    exact h2.symm
  have hT₄ : dieselExpandedTemp T₁ r γ rc = T₁ * rc ^ γ := by
    simp only [dieselExpandedTemp, dieselCutoffTemp, ottoCompressedTemp]
    rw [hdiv]
    field_simp
    linear_combination T₁ * hrc_pow
  have hQout : dieselHeatOut T₁ r γ Cv rc = Cv * T₁ * (rc ^ γ - 1) := by
    simp only [dieselHeatOut]
    rw [hT₄]
    ring
  have hQin : dieselHeatIn T₁ r γ Cv rc = γ * Cv * T₁ * r ^ (γ - 1) * (rc - 1) := by
    simp only [dieselHeatIn, dieselCutoffTemp, ottoCompressedTemp]
    ring
  have hnR : nR = Cv * (γ - 1) := by
    have h : Cv * (γ - 1) = nR := by
      rw [hγ]
      field_simp
    exact h.symm
  have hW : dieselNetWork T₁ r γ Cv nR rc =
      dieselHeatIn T₁ r γ Cv rc - dieselHeatOut T₁ r γ Cv rc := by
    simp only [dieselNetWork, dieselHeatIn, dieselHeatOut]
    rw [hnR]
    ring
  exact ⟨hT₄, hQout, hQin, hW⟩

/-- Nondegenerate loop: for `1 < rc < r`, `1 < γ` with `γ - 1 = nR / Cv`, `0 < Cv` and
`0 < T₁`, the heat input, the rejected heat and the net work are all positive. The net work is
positive because `rc ^ γ - 1 < γ * rc ^ (γ - 1) * (rc - 1) < γ * r ^ (γ - 1) * (rc - 1)`. -/
lemma diesel_heat_pos_netWork_pos {T₁ r γ Cv nR rc : ℝ} (hrc : 1 < rc) (hrcr : rc < r)
    (hγ₁ : 1 < γ) (hCv : 0 < Cv) (hT₁ : 0 < T₁) (hγ : γ - 1 = nR / Cv) :
    0 < dieselHeatIn T₁ r γ Cv rc ∧ 0 < dieselHeatOut T₁ r γ Cv rc ∧
      0 < dieselNetWork T₁ r γ Cv nR rc := by
  have hrc_pos : 0 < rc := by linarith
  have hr : 0 < r := lt_trans hrc_pos hrcr
  have hγ0 : 0 < γ := by linarith
  have hγ1 : 0 < γ - 1 := by linarith
  have hrc1 : 0 < rc - 1 := by linarith
  have hCv_ne : Cv ≠ 0 := ne_of_gt hCv
  obtain ⟨-, hQout, hQin, hW⟩ := diesel_closed_loop hr hrc_pos hCv_ne hγ
  have hQin_pos : 0 < dieselHeatIn T₁ r γ Cv rc := by
    rw [hQin]
    have hpow : 0 < r ^ (γ - 1) := Real.rpow_pos_of_pos hr _
    positivity
  have hQout_pos : 0 < dieselHeatOut T₁ r γ Cv rc := by
    rw [hQout]
    have hpow_gt1 : 1 < rc ^ γ := Real.one_lt_rpow hrc hγ0
    have hsub : 0 < rc ^ γ - 1 := by linarith
    positivity
  have hW_pos : 0 < dieselNetWork T₁ r γ Cv nR rc := by
    rw [hW, hQin, hQout]
    have hCvT₁ : 0 < Cv * T₁ := mul_pos hCv hT₁
    have hfc : StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ γ) :=
      strictConvexOn_rpow hγ₁
    have hf' : HasDerivAt (fun x : ℝ => x ^ γ) (γ * rc ^ (γ - 1)) rc :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hrc_pos))
    have htend := hf'.tendsto_slope
    have hsub : Set.Ioi rc ⊆ {rc}ᶜ := by
      intro y hy
      simp only [Set.mem_Ioi] at hy
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hy
    have htend' := htend.mono_left (nhdsWithin_mono rc hsub)
    have hev : ∀ᶠ y in nhdsWithin rc (Set.Ioi rc),
        (rc ^ γ - 1) / (rc - 1) ≤ slope (fun x : ℝ => x ^ γ) rc y := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [Set.mem_Ioi] at hy
      have hx : (1 : ℝ) ∈ Set.Ici 0 := Set.mem_Ici.mpr zero_le_one
      have hz : y ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_of_lt (lt_trans hrc_pos hy))
      have hlt := hfc.slope_strict_mono_adjacent hx hz hrc hy
      simp only [Real.one_rpow] at hlt
      rw [slope_def_field]
      exact le_of_lt hlt
    have hle : (rc ^ γ - 1) / (rc - 1) ≤ γ * rc ^ (γ - 1) := ge_of_tendsto htend' hev
    have hupper : rc ^ γ - 1 ≤ γ * rc ^ (γ - 1) * (rc - 1) :=
      (div_le_iff₀ hrc1).mp hle
    have hmono : rc ^ (γ - 1) < r ^ (γ - 1) :=
      Real.rpow_lt_rpow (le_of_lt hrc_pos) hrcr hγ1
    have hchain : rc ^ γ - 1 < γ * r ^ (γ - 1) * (rc - 1) := by
      have hpos : 0 < γ * (rc - 1) := mul_pos hγ0 hrc1
      have hstrict : γ * rc ^ (γ - 1) * (rc - 1) < γ * r ^ (γ - 1) * (rc - 1) := by
        have h := mul_lt_mul_of_pos_left hmono hpos
        linear_combination h
      linarith
    have hdiff : 0 < γ * r ^ (γ - 1) * (rc - 1) - (rc ^ γ - 1) := by linarith
    have heq : γ * Cv * T₁ * r ^ (γ - 1) * (rc - 1) - Cv * T₁ * (rc ^ γ - 1)
        = (Cv * T₁) * (γ * r ^ (γ - 1) * (rc - 1) - (rc ^ γ - 1)) := by ring
    rw [heq]
    exact mul_pos hCvT₁ hdiff
  exact ⟨hQin_pos, hQout_pos, hW_pos⟩

/-- Diesel efficiency: for `0 < r`, `0 < rc`, `rc ≠ 1`, `γ ≠ 0`, `T₁ ≠ 0`, `Cv ≠ 0` and
`γ - 1 = nR / Cv`, the work-to-heat ratio of the loop is
`Wnet / Qin = 1 - r ^ (1 - γ) * (rc ^ γ - 1) / (γ * (rc - 1)) = dieselEfficiency r γ rc`, and so
is `1 - Qout / Qin`. -/
lemma dieselNetWork_div_heatIn {T₁ r γ Cv nR rc : ℝ} (hr : 0 < r) (hrc : 0 < rc)
    (hrc₁ : rc ≠ 1) (hγ₀ : γ ≠ 0) (hT₁ : T₁ ≠ 0) (hCv : Cv ≠ 0) (hγ : γ - 1 = nR / Cv) :
    dieselNetWork T₁ r γ Cv nR rc / dieselHeatIn T₁ r γ Cv rc = dieselEfficiency r γ rc ∧
      1 - dieselHeatOut T₁ r γ Cv rc / dieselHeatIn T₁ r γ Cv rc = dieselEfficiency r γ rc := by
  have hrpow_ne : r ^ (γ - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr _)
  have hrc1 : rc - 1 ≠ 0 := sub_ne_zero.mpr hrc₁
  obtain ⟨-, hQout, hQin, hW⟩ := diesel_closed_loop hr hrc hCv hγ
  have hQin_ne : dieselHeatIn T₁ r γ Cv rc ≠ 0 := by
    rw [hQin]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hγ₀ hCv) hT₁) hrpow_ne) hrc1
  have hrpow_inv : r ^ (1 - γ) = (r ^ (γ - 1))⁻¹ := by
    have h : (1 - γ : ℝ) = -(γ - 1) := by ring
    rw [h, Real.rpow_neg (le_of_lt hr)]
  have hsecond : 1 - dieselHeatOut T₁ r γ Cv rc / dieselHeatIn T₁ r γ Cv rc
      = dieselEfficiency r γ rc := by
    rw [hQout, hQin]
    simp only [dieselEfficiency]
    rw [hrpow_inv]
    field_simp
  have hfirst : dieselNetWork T₁ r γ Cv nR rc / dieselHeatIn T₁ r γ Cv rc
      = dieselEfficiency r γ rc := by
    rw [hW, sub_div, div_self hQin_ne]
    exact hsecond
  exact ⟨hfirst, hsecond⟩

/-- At equal compression ratio the Diesel cycle is less efficient than the Otto cycle: on the
cycle domain `1 < rc < r` (so `1 < r`) and `1 < γ`, `dieselEfficiency r γ rc < ottoEfficiency r γ`,
because the factor `(rc ^ γ - 1) / (γ * (rc - 1))` exceeds one (strict Bernoulli inequality).
Outside that domain neither formula is the efficiency of the declared cycle. -/
lemma dieselEfficiency_lt_ottoEfficiency {r γ rc : ℝ} (hγ : 1 < γ) (hrc : 1 < rc)
    (hrcr : rc < r) :
    dieselEfficiency r γ rc < ottoEfficiency r γ := by
  have hr : 0 < r := by linarith
  have hγ0 : 0 < γ := by linarith
  have hrc1 : 0 < rc - 1 := by linarith
  have hdenom_pos : 0 < γ * (rc - 1) := mul_pos hγ0 hrc1
  have hbern : 1 + γ * (rc - 1) < rc ^ γ := by
    have hs : (-1 : ℝ) ≤ rc - 1 := by linarith
    have hs' : rc - 1 ≠ 0 := ne_of_gt hrc1
    have h := one_add_mul_self_lt_rpow_one_add hs hs' hγ
    have heq : (1 : ℝ) + (rc - 1) = rc := by ring
    rw [heq] at h
    exact h
  have hF_gt1 : 1 < (rc ^ γ - 1) / (γ * (rc - 1)) := by
    rw [lt_div_iff₀ hdenom_pos]
    linarith
  have hrpow_pos : 0 < r ^ (1 - γ) := Real.rpow_pos_of_pos hr _
  have hfactor : r ^ (1 - γ) * (rc ^ γ - 1) / (γ * (rc - 1))
      = r ^ (1 - γ) * ((rc ^ γ - 1) / (γ * (rc - 1))) := by ring
  have hlt : r ^ (1 - γ) < r ^ (1 - γ) * ((rc ^ γ - 1) / (γ * (rc - 1))) := by
    simpa using mul_lt_mul_of_pos_left hF_gt1 hrpow_pos
  simp only [dieselEfficiency, ottoEfficiency]
  rw [hfactor]
  linarith

/-- The ideal Diesel closed-state loop: for `1 < rc < r`, `1 < γ` with `γ - 1 = nR / Cv`,
constant `Cv > 0`, `T₁ > 0` and `V₁ > 0`, the states
`(T₁, V₁) → (T₂, V₁ / r) → (T₃, rc * (V₁ / r)) → (T₄, V₁) → (T₁, V₁)` have both adiabatic legs on
the `T * V ^ (γ - 1)` adiabat; under the ideal-gas law the cutoff state lies on the isobar of
state `2` (pressure `p₂ = nR * T₂ / V₂`) and the first law on that leg gives the heat input; the
net work is `Wnet = Qin - Qout`, the heats and the net work are positive, and the efficiency
`Wnet / Qin = 1 - r ^ (1 - γ) * (rc ^ γ - 1) / (γ * (rc - 1))` is below the Otto efficiency at the
same `r`. -/
lemma diesel_cycle {T₁ V₁ r γ Cv nR rc : ℝ} (hT₁ : 0 < T₁) (hV₁ : 0 < V₁) (hrc : 1 < rc)
    (hrcr : rc < r) (hγ₁ : 1 < γ) (hCv : 0 < Cv) (hγ : γ - 1 = nR / Cv) :
    ottoCompressedTemp T₁ r γ * (V₁ / r) ^ (γ - 1) = T₁ * V₁ ^ (γ - 1) ∧
      nR * ottoCompressedTemp T₁ r γ / (V₁ / r) * (rc * (V₁ / r)) =
        nR * dieselCutoffTemp T₁ r γ rc ∧
      Cv * (dieselCutoffTemp T₁ r γ rc - ottoCompressedTemp T₁ r γ) +
          nR * ottoCompressedTemp T₁ r γ / (V₁ / r) * (rc * (V₁ / r) - V₁ / r) =
        dieselHeatIn T₁ r γ Cv rc ∧
      dieselExpandedTemp T₁ r γ rc * V₁ ^ (γ - 1) =
        dieselCutoffTemp T₁ r γ rc * (rc * (V₁ / r)) ^ (γ - 1) ∧
      dieselNetWork T₁ r γ Cv nR rc =
        dieselHeatIn T₁ r γ Cv rc - dieselHeatOut T₁ r γ Cv rc ∧
      0 < dieselHeatIn T₁ r γ Cv rc ∧ 0 < dieselHeatOut T₁ r γ Cv rc ∧
      0 < dieselNetWork T₁ r γ Cv nR rc ∧
      dieselNetWork T₁ r γ Cv nR rc / dieselHeatIn T₁ r γ Cv rc =
        1 - r ^ (1 - γ) * (rc ^ γ - 1) / (γ * (rc - 1)) ∧
      dieselNetWork T₁ r γ Cv nR rc / dieselHeatIn T₁ r γ Cv rc < ottoEfficiency r γ := by
  have hrc_pos : 0 < rc := by linarith
  have hr : 0 < r := lt_trans hrc_pos hrcr
  have hr' : r ≠ 0 := ne_of_gt hr
  have hV₁' : V₁ ≠ 0 := ne_of_gt hV₁
  have hCv_ne : Cv ≠ 0 := ne_of_gt hCv
  have hT₁_ne : T₁ ≠ 0 := ne_of_gt hT₁
  have hγpos : 0 < γ := by linarith
  have hγ₀ : γ ≠ 0 := ne_of_gt hγpos
  have hrc₁ : rc ≠ 1 := ne_of_gt hrc
  have hCveq : Cv * (γ - 1) = nR := by
    rw [hγ]
    field_simp
  have hnR_pos : 0 < nR := by
    rw [← hCveq]
    exact mul_pos hCv (by linarith)
  have hnR : nR ≠ 0 := ne_of_gt hnR_pos
  have hcomp := (ottoCompression_adiabat hT₁ hV₁ hr hCv_ne hγ).2
  have hV₂_ne : V₁ / r ≠ 0 := div_ne_zero hV₁' hr'
  have hiso : nR * ottoCompressedTemp T₁ r γ / (V₁ / r) * (rc * (V₁ / r)) =
      nR * dieselCutoffTemp T₁ r γ rc := by
    simp only [dieselCutoffTemp]
    field_simp
  have h₂ : nR * ottoCompressedTemp T₁ r γ / (V₁ / r) * (V₁ / r) =
      nR * ottoCompressedTemp T₁ r γ := by
    field_simp
  have hfirstlaw := (dieselIsobaric_eos hnR hCv_ne hγ h₂ hiso).2
  have hexp := (dieselExpansion_adiabat hT₁ hV₁ hr hrc_pos hCv_ne hγ).2
  obtain ⟨-, -, -, hW⟩ := diesel_closed_loop hr hrc_pos hCv_ne hγ
  obtain ⟨hQin_pos, hQout_pos, hW_pos⟩ :=
    diesel_heat_pos_netWork_pos hrc hrcr hγ₁ hCv hT₁ hγ
  have hdiv := dieselNetWork_div_heatIn hr hrc_pos hrc₁ hγ₀ hT₁_ne hCv_ne hγ
  have h9 : dieselNetWork T₁ r γ Cv nR rc / dieselHeatIn T₁ r γ Cv rc =
      1 - r ^ (1 - γ) * (rc ^ γ - 1) / (γ * (rc - 1)) := by
    have h := hdiv.1
    simp only [dieselEfficiency] at h
    exact h
  have h10 : dieselNetWork T₁ r γ Cv nR rc / dieselHeatIn T₁ r γ Cv rc
      < ottoEfficiency r γ := by
    rw [hdiv.1]
    exact dieselEfficiency_lt_ottoEfficiency hγ₁ hrc hrcr
  exact ⟨hcomp, hiso, hfirstlaw, hexp, hW, hQin_pos, hQout_pos, hW_pos, h9, h10⟩

/-- The cutoff ratio one is a limit, not a value: as `rc` decreases to `1`, the Diesel
efficiency tends to the Otto efficiency at the same `r` (any `γ ≠ 0`), because
`(rc ^ γ - 1) / (rc - 1)` tends to the derivative `γ` of `rc ↦ rc ^ γ` at `1`. -/
lemma dieselEfficiency_tendsto_ottoEfficiency {r γ : ℝ} (hγ : γ ≠ 0) :
    Filter.Tendsto (fun rc => dieselEfficiency r γ rc) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (ottoEfficiency r γ)) := by
  have hderiv : HasDerivAt (fun x : ℝ => x ^ γ) γ 1 := by
    have h := Real.hasDerivAt_rpow_const (x := 1) (p := γ) (Or.inl one_ne_zero)
    simpa [Real.one_rpow] using h
  have hslope := hderiv.tendsto_slope
  have hsub : Set.Ioi (1 : ℝ) ⊆ ({(1 : ℝ)}ᶜ) := by
    intro y hy
    simp only [Set.mem_Ioi] at hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hy
  have hslope' := hslope.mono_left (nhdsWithin_mono (1 : ℝ) hsub)
  have heq : (fun rc => dieselEfficiency r γ rc) =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      (fun rc => 1 - (r ^ (1 - γ) / γ) * slope (fun x : ℝ => x ^ γ) 1 rc) := by
    filter_upwards [self_mem_nhdsWithin] with rc hrc
    simp only [Set.mem_Ioi] at hrc
    have hrc1 : rc - 1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < rc - 1)
    simp only [dieselEfficiency, slope_def_field, Real.one_rpow]
    field_simp
  have htend : Filter.Tendsto
      (fun rc => 1 - (r ^ (1 - γ) / γ) * slope (fun x : ℝ => x ^ γ) 1 rc)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 - (r ^ (1 - γ) / γ) * γ)) :=
    Filter.Tendsto.const_sub 1 (Filter.Tendsto.const_mul _ hslope')
  have hlim : (1 : ℝ) - (r ^ (1 - γ) / γ) * γ = ottoEfficiency r γ := by
    simp only [ottoEfficiency]
    field_simp
  rw [hlim] at htend
  exact Filter.Tendsto.congr' heq.symm htend

/-! ### Boundary cases -/

/-- Unit cutoff ratio: at `rc = 1` there is no heat addition and, for `0 < r`, the loop does no
net work, so the efficiency is the undefined `0 / 0`. Lean's value `dieselEfficiency r γ 1 = 1`
is not the Otto efficiency, which for `γ ≠ 0` is the limit as `rc` decreases to `1`
(`dieselEfficiency_tendsto_ottoEfficiency`). -/
lemma diesel_unit_cutoff {T₁ r γ Cv nR : ℝ} (hr : 0 < r) (hγ : γ ≠ 0) :
    dieselHeatIn T₁ r γ Cv 1 = 0 ∧ dieselNetWork T₁ r γ Cv nR 1 = 0 ∧
      dieselEfficiency r γ 1 = 1 ∧ dieselEfficiency r γ 1 ≠ ottoEfficiency r γ ∧
      Filter.Tendsto (fun rc => dieselEfficiency r γ rc) (nhdsWithin 1 (Set.Ioi 1))
        (nhds (ottoEfficiency r γ)) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hT₃ : dieselCutoffTemp T₁ r γ 1 = ottoCompressedTemp T₁ r γ := by
    simp [dieselCutoffTemp]
  have hT₄ : dieselExpandedTemp T₁ r γ 1 = T₁ := by
    have h1r : (0 : ℝ) ≤ 1 / r := le_of_lt (by positivity)
    have hmul : (r * (1 / r)) ^ (γ - 1) = r ^ (γ - 1) * (1 / r) ^ (γ - 1) :=
      Real.mul_rpow hr.le h1r
    have hr1 : r * (1 / r) = 1 := by field_simp
    have hpow : r ^ (γ - 1) * (1 / r) ^ (γ - 1) = 1 := by
      rw [← hmul, hr1, Real.one_rpow]
    simp only [dieselExpandedTemp, hT₃, ottoCompressedTemp]
    linear_combination T₁ * hpow
  have hQin : dieselHeatIn T₁ r γ Cv 1 = 0 := by
    simp [dieselHeatIn, hT₃]
  have hW : dieselNetWork T₁ r γ Cv nR 1 = 0 := by
    simp only [dieselNetWork, hT₃, hT₄]
    ring
  have hEff : dieselEfficiency r γ 1 = 1 := by
    simp [dieselEfficiency, Real.one_rpow]
  have hNe : dieselEfficiency r γ 1 ≠ ottoEfficiency r γ := by
    rw [hEff]
    simp only [ottoEfficiency]
    intro hcon
    have hpos : 0 < r ^ (1 - γ) := Real.rpow_pos_of_pos hr _
    have hzero : r ^ (1 - γ) = 0 := by linarith
    exact ne_of_gt hpos hzero
  exact ⟨hQin, hW, hEff, hNe, dieselEfficiency_tendsto_ottoEfficiency hγ⟩

/-- A cutoff above the compression ratio is not the declared cycle: for `0 < r < rc`,
`0 < V₁`, `0 < T₁`, `1 < γ` and `0 < Cv`, the cutoff volume `rc * (V₁ / r)` exceeds `V₁`, so the
adiabatic leg from the cutoff state to `V₁` is a compression: `T₃ < T₄`, and its work output
`Cv * (T₃ - T₄)` is negative. -/
lemma diesel_cutoff_above_ratio {T₁ V₁ r γ Cv rc : ℝ} (hr : 0 < r) (hrcr : r < rc)
    (hV₁ : 0 < V₁) (hT₁ : 0 < T₁) (hγ : 1 < γ) (hCv : 0 < Cv) :
    V₁ < rc * (V₁ / r) ∧ dieselCutoffTemp T₁ r γ rc < dieselExpandedTemp T₁ r γ rc ∧
      Cv * (dieselCutoffTemp T₁ r γ rc - dieselExpandedTemp T₁ r γ rc) < 0 := by
  have hrc_pos : 0 < rc := lt_trans hr hrcr
  have hrcr1 : 1 < rc / r := by
    rw [lt_div_iff₀ hr]
    linarith
  have heq : rc * (V₁ / r) = V₁ * (rc / r) := by ring
  have hV : V₁ < rc * (V₁ / r) := by
    rw [heq]
    simpa using mul_lt_mul_of_pos_left hrcr1 hV₁
  have hγ1 : 0 < γ - 1 := by linarith
  have hpow_gt1 : 1 < (rc / r) ^ (γ - 1) := Real.one_lt_rpow hrcr1 hγ1
  have hpow1 : 0 < r ^ (γ - 1) := Real.rpow_pos_of_pos hr _
  have hT₃_pos : 0 < dieselCutoffTemp T₁ r γ rc := by
    simp only [dieselCutoffTemp, ottoCompressedTemp]
    exact mul_pos hrc_pos (mul_pos hT₁ hpow1)
  have hT : dieselCutoffTemp T₁ r γ rc < dieselExpandedTemp T₁ r γ rc := by
    simp only [dieselExpandedTemp]
    simpa using mul_lt_mul_of_pos_left hpow_gt1 hT₃_pos
  have hW : Cv * (dieselCutoffTemp T₁ r γ rc - dieselExpandedTemp T₁ r γ rc) < 0 := by
    apply mul_neg_of_pos_of_neg hCv
    linarith
  exact ⟨hV, hT, hW⟩

end GasCycles
