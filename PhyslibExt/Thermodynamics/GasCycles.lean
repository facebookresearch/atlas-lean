/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

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
second-law input, as in `PhyslibExt.Chemistry.Thermodynamics.Entropy`) and the reversible
ideal-gas adiabat of `PhyslibExt.Chemistry.Thermodynamics.FirstLaw`.

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

## iii. Table of contents

- A. Coefficients of performance and their second-law bounds
- B. Ideal Otto cycle

## iv. References

- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 6:
  `COP_R = Q_L / W_net,in`, `COP_HP = Q_H / W_net,in`, the reversible values
  `1 / (T_H / T_L - 1)` and `1 / (1 - T_L / T_H)`, and the Clausius statement.
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 9:
  the ideal Otto cycle, `η = 1 - 1 / r ^ (k - 1)` under cold-air-standard assumptions.
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

end GasCycles
