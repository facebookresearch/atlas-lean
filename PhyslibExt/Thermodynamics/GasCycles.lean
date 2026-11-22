/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PhyslibExt.Chemistry.Thermodynamics.FirstLaw
public import PhyslibExt.Thermodynamics.ProcessPorts

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.PoissonAdiabat

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

Ideal Brayton cycle (section D). Per unit mass of an ideal gas with specific gas constant `R > 0`
and constant specific heat `cp > R` (so `γ = cp / (cp - R)`), from the compressor inlet
`(p₁, T₁)`, `T₁ > 0`, at pressure ratio `rp > 1` with `a = rp ^ (R / cp) > 1`: isentropic
compression to `rp p₁` at `T₂ = a T₁`, isobaric heat addition to a chosen turbine inlet temperature
`T₃ > T₂`, isentropic expansion back to `p₁` at `T₄ = T₃ / a`, and isobaric rejection. The
constructed isentropic legs lie on the `p v ^ γ` adiabat of the first-law module
(`adiabatic_invariant_pV` at unit mass, with the ideal-gas specific volumes `p v = R T`), and the
Poisson relation `EarthScience.poisson_temperature_ratio` forces `T₂` and `T₄` among all states on
those adiabats. Each leg is a steady-flow device with specific enthalpy `cp T`; its balance
`q - workOut w = cp T_out - cp T_in` (a model input) uses the engineering work output
`ProcessPorts.workOut`. Then `Qin = cp (T₃ - T₂) > 0`, `Qout = Qin / a`,
`Wnet = Qin - Qout = cp (1 - 1 / a) (T₃ - T₂) > 0` and `η = Wnet / Qin = 1 - 1 / a`, below the
Carnot efficiency `1 - T₁ / T₃` between the coldest state `T₁` and the hottest `T₃`.
A pressure ratio `rp > 1` alone does not give positive work: the work is positive exactly when
`T₃ > T₂`, and it vanishes at `T₃ = T₂` and at `rp = 1`.

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
- `GasCycles.braytonCompression_adiabat`, `GasCycles.braytonExpansion_adiabat`: both Brayton
  isentropic legs lie on the existing adiabat.
- `GasCycles.braytonCompressedTemp_eq_of_adiabat`, `GasCycles.braytonExpandedTemp_eq_of_adiabat`:
  the Poisson relation forces `T₂` and `T₄`.
- `GasCycles.brayton_leg_energy`: the four steady-flow leg balances give `Qin`, `Qout` and `Wnet`.
- `GasCycles.brayton_closed_loop`: `Qout = Qin / a` and
  `Wnet = Qin - Qout = cp (1 - 1 / a) (T₃ - T₂)`.
- `GasCycles.braytonNetWork_div_heatIn`, `GasCycles.braytonEfficiency_lt_carnot`:
  `η = 1 - 1 / a`, below the Carnot efficiency `1 - T₁ / T₃` between the coldest state `T₁` and
  the hottest `T₃` (for `0 < R < cp` and `rp > 1`).
- `GasCycles.brayton_cycle`: the nondegenerate loop under the cycle's hypotheses.
- `GasCycles.braytonNetWork_pos_iff`, `GasCycles.brayton_zero_work`: positive work exactly when
  `T₃ > T₂`; zero work at `T₃ = T₂` and at `rp = 1`.

## iii. Table of contents

- A. Coefficients of performance and their second-law bounds
- B. Ideal Otto cycle
- C. Ideal Diesel cycle
- D. Ideal Brayton cycle
  - D.1. States
  - D.2. The isentropic legs
  - D.3. Steady-flow legs and closure
  - D.4. Efficiency
  - D.5. Degenerate boundary

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
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 9:
  the ideal Brayton cycle under cold-air-standard assumptions,
  `T₂ / T₁ = (P₂ / P₁) ^ ((k - 1) / k)`, `q_in = cp (T₃ - T₂)`,
  `η = 1 - 1 / r_p ^ ((k - 1) / k)`, and the steady-flow energy balance of each device.
- John M. Wallace and Peter V. Hobbs, *Atmospheric Science: An Introductory Survey*, 2nd ed.,
  Academic Press, 2006, §3.4.3: Poisson's equation for adiabatic change.
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

/-! ## D. Ideal Brayton cycle -/

/-! ### D.1. States -/

/-- Isentropic temperature ratio `a = rp ^ (R / cp)` of the Brayton compressor and turbine at
pressure ratio `rp`, specific gas constant `R` and constant specific heat `cp`. Physical domain
`rp > 1`, `cp > R > 0`, where `a > 1`. -/
noncomputable def braytonTempRatio (rp R cp : ℝ) : ℝ := rp ^ (R / cp)

/-- Compressor exit temperature `T₂ = a T₁` of the isentropic compression from `(p₁, T₁)` to
`rp p₁`. -/
noncomputable def braytonCompressedTemp (T₁ rp R cp : ℝ) : ℝ := braytonTempRatio rp R cp * T₁

/-- Turbine exit temperature `T₄ = T₃ / a` of the isentropic expansion from `(rp p₁, T₃)` back to
`p₁`. -/
noncomputable def braytonExpandedTemp (T₃ rp R cp : ℝ) : ℝ := T₃ / braytonTempRatio rp R cp

/-- Heat added per unit mass on the isobaric leg `2 → 3`: `Qin = cp (T₃ - T₂)`. -/
noncomputable def braytonHeatIn (T₁ T₃ rp R cp : ℝ) : ℝ :=
  cp * (T₃ - braytonCompressedTemp T₁ rp R cp)

/-- Heat rejected per unit mass on the closing isobaric leg `4 → 1`: `Qout = cp (T₄ - T₁)`. -/
noncomputable def braytonHeatOut (T₁ T₃ rp R cp : ℝ) : ℝ :=
  cp * (braytonExpandedTemp T₃ rp R cp - T₁)

/-- Net work output per unit mass (engineering sign): the turbine output `cp (T₃ - T₄)` minus the
compressor input `cp (T₂ - T₁)`. -/
noncomputable def braytonNetWork (T₁ T₃ rp R cp : ℝ) : ℝ :=
  cp * (T₃ - braytonExpandedTemp T₃ rp R cp) - cp * (braytonCompressedTemp T₁ rp R cp - T₁)

/-- Ideal Brayton efficiency `1 - 1 / a` with `a = rp ^ (R / cp)`. -/
noncomputable def braytonEfficiency (rp R cp : ℝ) : ℝ := 1 - 1 / braytonTempRatio rp R cp

/-! ### D.2. The isentropic legs -/

/-- Compression leg on the existing adiabat: for `0 < R < cp`, `rp > 0`, `T₁ > 0`, `p₁ > 0` and
the ideal-gas specific volumes `p₁ v₁ = R T₁` and `(rp p₁) v₂ = R T₂` at `T₂ = a T₁`, the two
states satisfy the integrated adiabatic relation `(cp - R) log (T₂ / T₁) + R log (v₂ / v₁) = 0`
(`cv = cp - R`), hence the invariant `p v ^ γ`, `γ = cp / (cp - R)`, of `adiabatic_invariant_pV`
at unit mass. -/
lemma braytonCompression_adiabat {cp R rp T₁ p₁ v₁ v₂ : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 0 < rp) (hT₁ : 0 < T₁) (hp₁ : 0 < p₁) (hv₁ : p₁ * v₁ = R * T₁)
    (hv₂ : rp * p₁ * v₂ = R * braytonCompressedTemp T₁ rp R cp) :
    (cp - R) * Real.log (braytonCompressedTemp T₁ rp R cp / T₁) + R * Real.log (v₂ / v₁) = 0 ∧
      idealGasP 1 R (braytonCompressedTemp T₁ rp R cp) v₂ * v₂ ^ (cp / (cp - R)) =
        idealGasP 1 R T₁ v₁ * v₁ ^ (cp / (cp - R)) := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have hcp0 : cp ≠ 0 := ne_of_gt hcp
  have hcv : 0 < cp - R := sub_pos.mpr hRcp
  have hcv0 : cp - R ≠ 0 := ne_of_gt hcv
  have ha : 0 < braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    exact Real.rpow_pos_of_pos hrp _
  have ha0 : braytonTempRatio rp R cp ≠ 0 := ne_of_gt ha
  have hrp0 : rp ≠ 0 := ne_of_gt hrp
  have hp₁0 : p₁ ≠ 0 := ne_of_gt hp₁
  have hT₁0 : T₁ ≠ 0 := ne_of_gt hT₁
  have hT₂ : 0 < braytonCompressedTemp T₁ rp R cp := by
    simp only [braytonCompressedTemp]
    exact mul_pos ha hT₁
  have hv₁pos : 0 < v₁ := by
    have h : 0 < p₁ * v₁ := by rw [hv₁]; exact mul_pos hR hT₁
    exact (mul_pos_iff_of_pos_left hp₁).mp h
  have hv₂pos : 0 < v₂ := by
    have h : 0 < rp * p₁ * v₂ := by rw [hv₂]; exact mul_pos hR hT₂
    have hrp₁ : 0 < rp * p₁ := mul_pos hrp hp₁
    exact (mul_pos_iff_of_pos_left hrp₁).mp h
  have hv₁0 : v₁ ≠ 0 := ne_of_gt hv₁pos
  have hTratio : braytonCompressedTemp T₁ rp R cp / T₁ = braytonTempRatio rp R cp := by
    simp only [braytonCompressedTemp]
    field_simp
  have hvratio : v₂ / v₁ = braytonTempRatio rp R cp / rp := by
    have e1 : rp * p₁ * v₂ = braytonTempRatio rp R cp * (p₁ * v₁) := by
      rw [hv₁, hv₂]
      simp only [braytonCompressedTemp]
      ring
    have e2 : rp * v₂ = braytonTempRatio rp R cp * v₁ := by
      have hcancel : p₁ * (rp * v₂) = p₁ * (braytonTempRatio rp R cp * v₁) := by
        linear_combination e1
      exact mul_left_cancel₀ hp₁0 hcancel
    rw [div_eq_div_iff hv₁0 hrp0]
    linear_combination e2
  have hlog_a : Real.log (braytonTempRatio rp R cp) = (R / cp) * Real.log rp := by
    simp only [braytonTempRatio]
    exact Real.log_rpow hrp _
  have hlog_T : Real.log (braytonCompressedTemp T₁ rp R cp / T₁) = (R / cp) * Real.log rp := by
    rw [hTratio, hlog_a]
  have hlog_v : Real.log (v₂ / v₁) = Real.log (braytonTempRatio rp R cp) - Real.log rp := by
    rw [hvratio, Real.log_div ha0 hrp0]
  have had : (cp - R) * Real.log (braytonCompressedTemp T₁ rp R cp / T₁) +
      R * Real.log (v₂ / v₁) = 0 := by
    rw [hlog_T, hlog_v, hlog_a]
    field_simp
    ring
  refine ⟨had, ?_⟩
  have hγ : cp / (cp - R) - 1 = 1 * R / (cp - R) := by
    field_simp
    ring
  have had' : (cp - R) * Real.log (braytonCompressedTemp T₁ rp R cp / T₁) +
      1 * R * Real.log (v₂ / v₁) = 0 := by
    linear_combination had
  exact adiabatic_invariant_pV 1 R T₁ (braytonCompressedTemp T₁ rp R cp) v₁ v₂ (cp - R)
    (cp / (cp - R)) (by norm_num) hR hT₁ hT₂ hv₁pos hv₂pos hcv0 hγ had'

/-- Expansion leg on the existing adiabat: for `0 < R < cp`, `rp > 0`, `T₃ > 0`, `p₁ > 0` and
the ideal-gas specific volumes `(rp p₁) v₃ = R T₃` and `p₁ v₄ = R T₄` at `T₄ = T₃ / a`, the two
states satisfy the integrated adiabatic relation, hence the invariant `p v ^ γ`. -/
lemma braytonExpansion_adiabat {cp R rp T₃ p₁ v₃ v₄ : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 0 < rp) (hT₃ : 0 < T₃) (hp₁ : 0 < p₁) (hv₃ : rp * p₁ * v₃ = R * T₃)
    (hv₄ : p₁ * v₄ = R * braytonExpandedTemp T₃ rp R cp) :
    (cp - R) * Real.log (braytonExpandedTemp T₃ rp R cp / T₃) + R * Real.log (v₄ / v₃) = 0 ∧
      idealGasP 1 R (braytonExpandedTemp T₃ rp R cp) v₄ * v₄ ^ (cp / (cp - R)) =
        idealGasP 1 R T₃ v₃ * v₃ ^ (cp / (cp - R)) := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have hcp0 : cp ≠ 0 := ne_of_gt hcp
  have hcv : 0 < cp - R := sub_pos.mpr hRcp
  have hcv0 : cp - R ≠ 0 := ne_of_gt hcv
  have ha : 0 < braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    exact Real.rpow_pos_of_pos hrp _
  have ha0 : braytonTempRatio rp R cp ≠ 0 := ne_of_gt ha
  have hrp0 : rp ≠ 0 := ne_of_gt hrp
  have hp₁0 : p₁ ≠ 0 := ne_of_gt hp₁
  have hT₃0 : T₃ ≠ 0 := ne_of_gt hT₃
  have hT₄ : 0 < braytonExpandedTemp T₃ rp R cp := by
    simp only [braytonExpandedTemp]
    exact div_pos hT₃ ha
  have hv₃pos : 0 < v₃ := by
    have h : 0 < rp * p₁ * v₃ := by rw [hv₃]; exact mul_pos hR hT₃
    have hrp₁ : 0 < rp * p₁ := mul_pos hrp hp₁
    exact (mul_pos_iff_of_pos_left hrp₁).mp h
  have hv₄pos : 0 < v₄ := by
    have h : 0 < p₁ * v₄ := by rw [hv₄]; exact mul_pos hR hT₄
    exact (mul_pos_iff_of_pos_left hp₁).mp h
  have hv₃0 : v₃ ≠ 0 := ne_of_gt hv₃pos
  have hTratio : braytonExpandedTemp T₃ rp R cp / T₃ = 1 / braytonTempRatio rp R cp := by
    simp only [braytonExpandedTemp]
    field_simp
  have hvratio : v₄ / v₃ = rp / braytonTempRatio rp R cp := by
    have e1 : braytonTempRatio rp R cp * (p₁ * v₄) = rp * p₁ * v₃ := by
      rw [hv₃, hv₄]
      simp only [braytonExpandedTemp]
      field_simp
    have e2 : braytonTempRatio rp R cp * v₄ = rp * v₃ := by
      have hcancel : p₁ * (braytonTempRatio rp R cp * v₄) = p₁ * (rp * v₃) := by
        linear_combination e1
      exact mul_left_cancel₀ hp₁0 hcancel
    rw [div_eq_div_iff hv₃0 ha0]
    linear_combination e2
  have hlog_a : Real.log (braytonTempRatio rp R cp) = (R / cp) * Real.log rp := by
    simp only [braytonTempRatio]
    exact Real.log_rpow hrp _
  have hlog_T : Real.log (braytonExpandedTemp T₃ rp R cp / T₃) =
      -((R / cp) * Real.log rp) := by
    rw [hTratio, Real.log_div one_ne_zero ha0, Real.log_one, zero_sub, hlog_a]
  have hlog_v : Real.log (v₄ / v₃) = Real.log rp - Real.log (braytonTempRatio rp R cp) := by
    rw [hvratio, Real.log_div hrp0 ha0]
  have had : (cp - R) * Real.log (braytonExpandedTemp T₃ rp R cp / T₃) +
      R * Real.log (v₄ / v₃) = 0 := by
    rw [hlog_T, hlog_v, hlog_a]
    field_simp
    ring
  refine ⟨had, ?_⟩
  have hγ : cp / (cp - R) - 1 = 1 * R / (cp - R) := by
    field_simp
    ring
  have had' : (cp - R) * Real.log (braytonExpandedTemp T₃ rp R cp / T₃) +
      1 * R * Real.log (v₄ / v₃) = 0 := by
    linear_combination had
  exact adiabatic_invariant_pV 1 R T₃ (braytonExpandedTemp T₃ rp R cp) v₃ v₄ (cp - R)
    (cp / (cp - R)) (by norm_num) hR hT₃ hT₄ hv₃pos hv₄pos hcv0 hγ had'

/-- The compressor exit temperature is forced by the existing isentrope: if a state at pressure
`rp p₁` with specific volume `v > 0` and temperature `T` obeys the ideal-gas law and lies on the
adiabat `p₁ v₁ ^ γ = (rp p₁) v ^ γ`, `γ = cp / (cp - R)`, through the inlet state `p₁ v₁ = R T₁`,
then `T = T₂ = a T₁` (`poisson_temperature_ratio`). -/
lemma braytonCompressedTemp_eq_of_adiabat {cp R rp T₁ p₁ v₁ T v : ℝ} (hR : 0 < R)
    (hRcp : R < cp) (hrp : 0 < rp) (hT₁ : 0 < T₁) (hp₁ : 0 < p₁) (hv : 0 < v)
    (hgas₁ : p₁ * v₁ = R * T₁) (hgas : rp * p₁ * v = R * T)
    (had : p₁ * v₁ ^ (cp / (cp - R)) = rp * p₁ * v ^ (cp / (cp - R))) :
    T = braytonCompressedTemp T₁ rp R cp := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have hv₁pos : 0 < v₁ := by
    have h : 0 < p₁ * v₁ := by rw [hgas₁]; exact mul_pos hR hT₁
    exact (mul_pos_iff_of_pos_left hp₁).mp h
  have hp₂ : 0 < rp * p₁ := mul_pos hrp hp₁
  have hP := EarthScience.poisson_temperature_ratio hp₁ hp₂ hv₁pos hv hT₁ hR hRcp hcp
    rfl hgas₁ hgas had
  have hp₁0 : p₁ ≠ 0 := ne_of_gt hp₁
  have hpr : rp * p₁ / p₁ = rp := by
    rw [div_eq_iff hp₁0]
  rw [hpr] at hP
  simp only [braytonCompressedTemp, braytonTempRatio]
  linear_combination hP

/-- The turbine exit temperature is forced by the existing isentrope: if a state at pressure
`p₁` with specific volume `v > 0` and temperature `T` obeys the ideal-gas law and lies on the
adiabat `(rp p₁) v₃ ^ γ = p₁ v ^ γ` through the turbine inlet state `(rp p₁) v₃ = R T₃`, then
`T = T₄ = T₃ / a` (`poisson_temperature_ratio`). -/
lemma braytonExpandedTemp_eq_of_adiabat {cp R rp T₃ p₁ v₃ T v : ℝ} (hR : 0 < R)
    (hRcp : R < cp) (hrp : 0 < rp) (hT₃ : 0 < T₃) (hp₁ : 0 < p₁) (hv : 0 < v)
    (hgas₃ : rp * p₁ * v₃ = R * T₃) (hgas : p₁ * v = R * T)
    (had : rp * p₁ * v₃ ^ (cp / (cp - R)) = p₁ * v ^ (cp / (cp - R))) :
    T = braytonExpandedTemp T₃ rp R cp := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have hv₃pos : 0 < v₃ := by
    have h : 0 < rp * p₁ * v₃ := by rw [hgas₃]; exact mul_pos hR hT₃
    have hrp₁ : 0 < rp * p₁ := mul_pos hrp hp₁
    exact (mul_pos_iff_of_pos_left hrp₁).mp h
  have hp₃ : 0 < rp * p₁ := mul_pos hrp hp₁
  have hP := EarthScience.poisson_temperature_ratio hp₃ hp₁ hv₃pos hv hT₃ hR hRcp hcp
    rfl hgas₃ hgas had
  have hp₁0 : p₁ ≠ 0 := ne_of_gt hp₁
  have hrp0 : rp ≠ 0 := ne_of_gt hrp
  have hpr : p₁ / (rp * p₁) = 1 / rp := by
    field_simp
  have hrw : (1 / rp) ^ (R / cp) = 1 / braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    rw [Real.div_rpow zero_le_one (le_of_lt hrp), Real.one_rpow]
  rw [hpr, hrw] at hP
  simp only [braytonExpandedTemp]
  rw [mul_one_div] at hP
  exact hP

/-! ### D.3. Steady-flow legs and closure -/

/-- The four matched legs as steady-flow devices: with specific enthalpy `cp T` and the per-mass
steady-flow balance `q - workOut w = cp T_out - cp T_in` on each leg (heat `q` in, work `w` done
on the gas, engineering output `workOut w`), the adiabatic compressor and turbine (`q = 0`) and
the work-free heater and cooler (`w = 0`) give the heat added `q₂₃ = Qin`, the heat rejected
`-q₄₁ = Qout` and the net shaft output `workOut w₁₂ + workOut w₃₄ = Wnet`, which equals the net
heat `q₂₃ + q₄₁` because the enthalpy changes cancel around the closed loop. -/
lemma brayton_leg_energy {cp R rp T₁ T₃ q₁₂ q₂₃ q₃₄ q₄₁ w₁₂ w₂₃ w₃₄ w₄₁ : ℝ}
    (h₁₂ : q₁₂ - ProcessPorts.workOut w₁₂ = cp * braytonCompressedTemp T₁ rp R cp - cp * T₁)
    (h₂₃ : q₂₃ - ProcessPorts.workOut w₂₃ = cp * T₃ - cp * braytonCompressedTemp T₁ rp R cp)
    (h₃₄ : q₃₄ - ProcessPorts.workOut w₃₄ = cp * braytonExpandedTemp T₃ rp R cp - cp * T₃)
    (h₄₁ : q₄₁ - ProcessPorts.workOut w₄₁ = cp * T₁ - cp * braytonExpandedTemp T₃ rp R cp)
    (hq₁₂ : q₁₂ = 0) (hq₃₄ : q₃₄ = 0) (hw₂₃ : w₂₃ = 0) (hw₄₁ : w₄₁ = 0) :
    q₂₃ = braytonHeatIn T₁ T₃ rp R cp ∧ -q₄₁ = braytonHeatOut T₁ T₃ rp R cp ∧
      ProcessPorts.workOut w₁₂ + ProcessPorts.workOut w₃₄ = braytonNetWork T₁ T₃ rp R cp ∧
      ProcessPorts.workOut w₁₂ + ProcessPorts.workOut w₃₄ = q₂₃ + q₄₁ := by
  simp only [ProcessPorts.workOut, braytonHeatIn, braytonHeatOut, braytonNetWork]
    at h₁₂ h₂₃ h₃₄ h₄₁ ⊢
  rw [hq₁₂] at h₁₂
  rw [hw₂₃] at h₂₃
  rw [hq₃₄] at h₃₄
  rw [hw₄₁] at h₄₁
  simp only [neg_zero, sub_zero, zero_sub, neg_neg] at h₁₂ h₂₃ h₃₄ h₄₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination h₂₃
  · linear_combination -h₄₁
  · linear_combination -h₁₂ - h₃₄
  · linear_combination -h₁₂ - h₂₃ - h₃₄ - h₄₁

/-- The loop closes: for `rp > 0` the turbine expands by the compressor's pressure ratio, so the
rejected heat is `Qout = Qin / a`; the net work is the net heat, `Wnet = Qin - Qout`; and
`Wnet = cp (1 - 1 / a) (T₃ - T₂)`. -/
lemma brayton_closed_loop {cp R rp T₁ T₃ : ℝ} (hrp : 0 < rp) :
    braytonHeatOut T₁ T₃ rp R cp = braytonHeatIn T₁ T₃ rp R cp / braytonTempRatio rp R cp ∧
      braytonNetWork T₁ T₃ rp R cp =
        braytonHeatIn T₁ T₃ rp R cp - braytonHeatOut T₁ T₃ rp R cp ∧
      braytonNetWork T₁ T₃ rp R cp =
        cp * (1 - 1 / braytonTempRatio rp R cp) * (T₃ - braytonCompressedTemp T₁ rp R cp) := by
  have ha : 0 < braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    exact Real.rpow_pos_of_pos hrp _
  have ha0 : braytonTempRatio rp R cp ≠ 0 := ne_of_gt ha
  simp only [braytonHeatIn, braytonHeatOut, braytonNetWork, braytonCompressedTemp,
    braytonExpandedTemp]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
  · ring
  · field_simp

/-- Nondegenerate loop: for `0 < R < cp`, `rp > 1` and `T₃ > T₂`, the heat added, the heat
rejected and the net work are all positive. -/
lemma brayton_heat_work_pos {cp R rp T₁ T₃ : ℝ} (hR : 0 < R) (hRcp : R < cp) (hrp : 1 < rp)
    (hT₃ : braytonCompressedTemp T₁ rp R cp < T₃) :
    0 < braytonHeatIn T₁ T₃ rp R cp ∧ 0 < braytonHeatOut T₁ T₃ rp R cp ∧
      0 < braytonNetWork T₁ T₃ rp R cp := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have he : 0 < R / cp := div_pos hR hcp
  have ha1 : 1 < braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    exact Real.one_lt_rpow hrp he
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have hrp0 : 0 < rp := lt_trans zero_lt_one hrp
  have hsub : 0 < T₃ - braytonCompressedTemp T₁ rp R cp := sub_pos.mpr hT₃
  have hQin : 0 < braytonHeatIn T₁ T₃ rp R cp := by
    simp only [braytonHeatIn]
    exact mul_pos hcp hsub
  have hloop := brayton_closed_loop (cp := cp) (R := R) (T₁ := T₁) (T₃ := T₃) hrp0
  have hQout : 0 < braytonHeatOut T₁ T₃ rp R cp := by
    rw [hloop.1]
    exact div_pos hQin ha
  have hW : 0 < braytonNetWork T₁ T₃ rp R cp := by
    rw [hloop.2.2]
    have h1 : (1 : ℝ) / braytonTempRatio rp R cp < 1 := (div_lt_one ha).mpr ha1
    exact mul_pos (mul_pos hcp (sub_pos.mpr h1)) hsub
  exact ⟨hQin, hQout, hW⟩

/-! ### D.4. Efficiency -/

/-- Brayton efficiency: for `rp > 0` and nonzero heat input, `Wnet / Qin = 1 - 1 / a`, and so is
`1 - Qout / Qin`. -/
lemma braytonNetWork_div_heatIn {cp R rp T₁ T₃ : ℝ} (hrp : 0 < rp)
    (hQ : braytonHeatIn T₁ T₃ rp R cp ≠ 0) :
    braytonNetWork T₁ T₃ rp R cp / braytonHeatIn T₁ T₃ rp R cp = braytonEfficiency rp R cp ∧
      1 - braytonHeatOut T₁ T₃ rp R cp / braytonHeatIn T₁ T₃ rp R cp =
        braytonEfficiency rp R cp := by
  have ha : 0 < braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    exact Real.rpow_pos_of_pos hrp _
  have ha0 : braytonTempRatio rp R cp ≠ 0 := ne_of_gt ha
  have hloop := brayton_closed_loop (cp := cp) (R := R) (T₁ := T₁) (T₃ := T₃) hrp
  simp only [braytonEfficiency]
  rw [hloop.2.1, hloop.1]
  constructor
  · field_simp
  · field_simp

/-- The Brayton efficiency is below the Carnot efficiency between the loop's extreme
temperatures: for `0 < R < cp` and `rp > 1` (so `a > 1`), `T₁ > 0` and a turbine inlet temperature
`T₃ > T₂ = a T₁`, the compressor inlet `T₁` is the coldest and the turbine inlet `T₃` the hottest
of the four states (`T₁ < T₂ < T₃` and `T₁ < T₄ < T₃`), and `1 - 1 / a < 1 - T₁ / T₃`. -/
lemma braytonEfficiency_lt_carnot {cp R rp T₁ T₃ : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 1 < rp) (hT₁ : 0 < T₁) (hT₃ : braytonCompressedTemp T₁ rp R cp < T₃) :
    T₁ < braytonCompressedTemp T₁ rp R cp ∧ T₁ < braytonExpandedTemp T₃ rp R cp ∧
      braytonExpandedTemp T₃ rp R cp < T₃ ∧ braytonEfficiency rp R cp < 1 - T₁ / T₃ := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have ha1 : 1 < braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    exact Real.one_lt_rpow hrp (div_pos hR hcp)
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have hT₂ : T₁ < braytonCompressedTemp T₁ rp R cp := by
    simp only [braytonCompressedTemp]
    nlinarith
  have hT₃pos : 0 < T₃ := by linarith
  have hT₄ : T₁ < braytonExpandedTemp T₃ rp R cp := by
    simp only [braytonExpandedTemp, braytonCompressedTemp] at hT₃ ⊢
    rw [lt_div_iff₀ ha]
    linear_combination hT₃
  have hT₄' : braytonExpandedTemp T₃ rp R cp < T₃ := by
    simp only [braytonExpandedTemp]
    exact div_lt_self hT₃pos ha1
  refine ⟨hT₂, hT₄, hT₄', ?_⟩
  simp only [braytonEfficiency, braytonCompressedTemp] at hT₃ ⊢
  have h : T₁ / T₃ < 1 / braytonTempRatio rp R cp := by
    rw [div_lt_div_iff₀ hT₃pos ha, one_mul]
    linear_combination hT₃
  linarith

/-- **The nondegenerate Brayton loop.** For `cp > R > 0`, `rp > 1`, `T₁ > 0`,
`a = rp ^ (R / cp)`, `T₂ = a T₁` and a turbine inlet temperature `T₃ > T₂` (with `T₄ = T₃ / a`):
the heat added `Qin = cp (T₃ - T₂)` is positive, `Wnet = cp (1 - 1 / a) (T₃ - T₂) > 0`, and the
efficiency `Wnet / Qin = 1 - 1 / a` is below `1 - T₁ / T₃`. -/
lemma brayton_cycle {cp R rp T₁ T₃ : ℝ} (hR : 0 < R) (hRcp : R < cp) (hrp : 1 < rp)
    (hT₁ : 0 < T₁) (hT₃ : braytonCompressedTemp T₁ rp R cp < T₃) :
    0 < braytonHeatIn T₁ T₃ rp R cp ∧
      braytonNetWork T₁ T₃ rp R cp =
        cp * (1 - 1 / braytonTempRatio rp R cp) * (T₃ - braytonCompressedTemp T₁ rp R cp) ∧
      0 < braytonNetWork T₁ T₃ rp R cp ∧
      braytonNetWork T₁ T₃ rp R cp / braytonHeatIn T₁ T₃ rp R cp =
        1 - 1 / braytonTempRatio rp R cp ∧
      1 - 1 / braytonTempRatio rp R cp < 1 - T₁ / T₃ := by
  have hrp0 : 0 < rp := lt_trans zero_lt_one hrp
  have hpos := brayton_heat_work_pos hR hRcp hrp hT₃
  have hloop := brayton_closed_loop (cp := cp) (R := R) (T₁ := T₁) (T₃ := T₃) hrp0
  have hdiv := (braytonNetWork_div_heatIn hrp0 (ne_of_gt hpos.1)).1
  have hcarnot := (braytonEfficiency_lt_carnot hR hRcp hrp hT₁ hT₃).2.2.2
  simp only [braytonEfficiency] at hdiv hcarnot
  exact ⟨hpos.1, hloop.2.2, hpos.2.2, hdiv, hcarnot⟩

/-! ### D.5. Degenerate boundary -/

/-- A pressure ratio `rp > 1` alone does not give positive work: for `0 < R < cp` and `rp > 1`
the net work is positive exactly when `T₃ > T₂`. -/
lemma braytonNetWork_pos_iff {cp R rp T₁ T₃ : ℝ} (hR : 0 < R) (hRcp : R < cp) (hrp : 1 < rp) :
    0 < braytonNetWork T₁ T₃ rp R cp ↔ braytonCompressedTemp T₁ rp R cp < T₃ := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have he : 0 < R / cp := div_pos hR hcp
  have ha1 : 1 < braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    exact Real.one_lt_rpow hrp he
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have hrp0 : 0 < rp := lt_trans zero_lt_one hrp
  have hloop := (brayton_closed_loop (cp := cp) (R := R) (T₁ := T₁) (T₃ := T₃) hrp0).2.2
  have hC : 0 < cp * (1 - 1 / braytonTempRatio rp R cp) := by
    have h1 : (1 : ℝ) / braytonTempRatio rp R cp < 1 := (div_lt_one ha).mpr ha1
    exact mul_pos hcp (sub_pos.mpr h1)
  rw [hloop, mul_pos_iff_of_pos_left hC]
  exact sub_pos

/-- Degenerate zero-work boundary: for `rp > 0` the net work vanishes at `T₃ = T₂` (no heat
added), and at `rp = 1` (no compression, `a = 1`) it vanishes for every `T₃`. -/
lemma brayton_zero_work {cp R rp T₁ T₃ : ℝ} (hrp : 0 < rp) :
    (T₃ = braytonCompressedTemp T₁ rp R cp → braytonNetWork T₁ T₃ rp R cp = 0) ∧
      braytonNetWork T₁ T₃ 1 R cp = 0 := by
  constructor
  · intro hT
    have hloop := (brayton_closed_loop (cp := cp) (R := R) (T₁ := T₁) (T₃ := T₃) hrp).2.2
    rw [hloop, hT, sub_self, mul_zero]
  · simp only [braytonNetWork, braytonCompressedTemp, braytonExpandedTemp, braytonTempRatio,
      Real.one_rpow, one_mul, div_one, sub_self, mul_zero]

end GasCycles
