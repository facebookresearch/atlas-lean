/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PhyslibExt.ContinuumMechanics.ControlVolumes

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.PoissonAdiabat

/-!
# Perfect-gas ports: the stagnation state adapter

## i. Overview

A calorically perfect gas with specific gas constant `R > 0` and heat-capacity ratio `γ > 1` has
the constant specific heats `cv = R / (γ - 1)` and `cp = γ R / (γ - 1)`, internal energy
`e = cv T` and the ideal-gas law `p = ρ R T`. The specific enthalpy `h = e + p / ρ` of the
energy ports (`ControlVolumes.specificEnthalpy`, flow work counted once) is then `cp T`.

A gas at absolute temperature `T > 0` with velocity coordinate `u` has sound speed `a`,
`a ^ 2 = γ R T`, and Mach number `M = |u| / a`, the speed `|u|` over `a` as in
`EngineeringScaling.machNumber`. Its stagnation temperature `T0` is fixed by the stagnation
energy balance `cp T + u ^ 2 / 2 = cp T0` (the port enthalpy plus kinetic energy, brought to
rest without heat or work), which gives `T0 / T = 1 + (γ - 1) M ^ 2 / 2`.

The energy balance fixes `T0` but not the stagnation pressure: a deceleration with losses keeps
`T0` and lowers `p0`. Only a separately declared isentropic connection
`p / ρ ^ γ = p0 / ρ0 ^ γ` between the static and the stagnation state, with the ideal-gas law at
both, gives the isentrope `T0 = T (p0 / p) ^ (R / cp)` (`EarthScience.poisson_temperature_ratio`
with the specific volumes `1 / ρ` and `1 / ρ0`), hence `p0 / p = (T0 / T) ^ (γ / (γ - 1))` and
`ρ0 / ρ = (T0 / T) ^ (1 / (γ - 1))`.

## ii. Key results

- `FluidDynamics.PerfectGasPorts.specificEnthalpy_perfectGas`: the port enthalpy is `cp T`.
- `FluidDynamics.PerfectGasPorts.stagnation_temperature_ratio`:
  `T0 / T = 1 + (γ - 1) M ^ 2 / 2`.
- `FluidDynamics.PerfectGasPorts.stagnation_pressure_ratio`,
  `FluidDynamics.PerfectGasPorts.stagnation_density_ratio`: the stagnation pressure and density
  ratios through the isentrope.
- `FluidDynamics.PerfectGasPorts.temperature_lt_stagnation`: `M > 0` gives `T < T0`.
- `FluidDynamics.PerfectGasPorts.stagnation_eq_static_of_mach_eq_zero`: at `M = 0` the
  stagnation state is the static state.
- `FluidDynamics.PerfectGasPorts.stagnation_energy_not_isentropic`: the energy balance alone does
  not give the isentropic pressure ratio.

## iii. Table of contents

- A. Port enthalpy of a calorically perfect gas
- B. Stagnation temperature
- C. Stagnation pressure and density through the isentrope
- D. Boundary cases

## iv. References

- J. D. Anderson, *Modern Compressible Flow*, 3rd ed., McGraw-Hill, 2003, ch. 3: the total
  temperature `T0 / T = 1 + (γ - 1) M ^ 2 / 2` from the adiabatic energy equation, and the total
  pressure and density ratios of an isentropic deceleration.
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, the
  compressible-flow chapter: stagnation enthalpy `h0 = h + V ^ 2 / 2` and stagnation properties.
- ISO 80000-11, *Quantities and units, Part 11: Characteristic numbers*: the Mach number.
- `EarthScience.poisson_temperature_ratio` (`PhyslibExt.EarthScience.PoissonAdiabat`) and
  `ControlVolumes.specificEnthalpy` (`PhyslibExt.ContinuumMechanics.ControlVolumes`).
-/

@[expose] public section

namespace FluidDynamics.PerfectGasPorts

/-! ## A. Port enthalpy of a calorically perfect gas -/

/-- The port enthalpy of a calorically perfect gas is `cp T`: with `cv = R / (γ - 1)`, internal
energy `e = cv T`, the ideal-gas law `p = ρ R T` at a density `ρ ≠ 0`, and `cp = γ R / (γ - 1)`,
the specific enthalpy `h = e + p / ρ` of the energy ports is `cp T`. Internal energy and
enthalpy are both measured from zero at `T = 0`. -/
lemma specificEnthalpy_perfectGas {γ R T ρ cv cp e p : ℝ} (hγ : 1 < γ) (hρ : ρ ≠ 0)
    (hcv : cv = R / (γ - 1)) (hcp : cp = γ * R / (γ - 1)) (he : e = cv * T)
    (hp : p = ρ * R * T) :
    ControlVolumes.specificEnthalpy e p ρ = cp * T := by
  have hγ1 : γ - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hγ)
  unfold ControlVolumes.specificEnthalpy
  rw [he, hcv, hp, hcp]
  field_simp
  ring

/-! ## B. Stagnation temperature -/

/-- **Stagnation temperature.** For `γ > 1`, `R > 0`, `T > 0`, `cp = γ R / (γ - 1)`, a sound
speed `a` with `a ^ 2 = γ R T`, the Mach number `M = |u| / a` of the velocity coordinate `u`, and
the stagnation energy balance `cp T + u ^ 2 / 2 = cp T0`, the stagnation-to-static temperature
ratio is `T0 / T = 1 + (γ - 1) M ^ 2 / 2`. No entropy hypothesis enters. -/
lemma stagnation_temperature_ratio {γ R T T0 cp a u M : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hT : 0 < T) (hcp : cp = γ * R / (γ - 1)) (ha2 : a ^ 2 = γ * R * T) (hM : M = |u| / a)
    (hen : cp * T + u ^ 2 / 2 = cp * T0) :
    T0 / T = 1 + (γ - 1) * M ^ 2 / 2 := by
  have hγ1pos : 0 < γ - 1 := by linarith
  have hγ1 : γ - 1 ≠ 0 := ne_of_gt hγ1pos
  have hγpos : 0 < γ := by linarith
  have hγ0 : γ ≠ 0 := ne_of_gt hγpos
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hcp_pos : 0 < cp := by rw [hcp]; exact div_pos (mul_pos hγpos hR) hγ1pos
  have hcp0 : cp ≠ 0 := ne_of_gt hcp_pos
  have hT_ne : T ≠ 0 := ne_of_gt hT
  have ha2pos : 0 < a ^ 2 := by rw [ha2]; positivity
  have ha_ne : a ≠ 0 := fun h => ne_of_gt ha2pos (by rw [h]; norm_num)
  have hM2 : M ^ 2 = u ^ 2 / a ^ 2 := by rw [hM, div_pow, sq_abs]
  have hT0eq : T0 = T + u ^ 2 / (2 * cp) := by
    have h2cp : (2 : ℝ) * cp ≠ 0 := ne_of_gt (mul_pos two_pos hcp_pos)
    field_simp
    linarith [hen]
  rw [hT0eq, hM2, ha2, hcp]
  have hGRT : γ * R * T ≠ 0 := mul_ne_zero (mul_ne_zero hγ0 hR0) hT_ne
  have hcp' : γ * R / (γ - 1) ≠ 0 := div_ne_zero (mul_ne_zero hγ0 hR0) hγ1
  have h2cp' : 2 * (γ * R / (γ - 1)) ≠ 0 := mul_ne_zero two_ne_zero hcp'
  field_simp

/-! ## C. Stagnation pressure and density through the isentrope -/

/-- **Stagnation pressure.** Under the hypotheses of `stagnation_temperature_ratio`, with
positive densities `ρ`, `ρ0`, the ideal-gas law `p = ρ R T` and `p0 = ρ0 R T0` at the static and
the stagnation state, and the declared isentropic connection `p / ρ ^ γ = p0 / ρ0 ^ γ`, the
isentrope gives `p0 / p = (T0 / T) ^ (γ / (γ - 1))`, hence
`p0 / p = (1 + (γ - 1) M ^ 2 / 2) ^ (γ / (γ - 1))`. -/
lemma stagnation_pressure_ratio {γ R T T0 cp a u M ρ ρ0 p p0 : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hT : 0 < T) (hcp : cp = γ * R / (γ - 1)) (ha2 : a ^ 2 = γ * R * T) (hM : M = |u| / a)
    (hen : cp * T + u ^ 2 / 2 = cp * T0) (hρ : 0 < ρ) (hρ0 : 0 < ρ0) (hp : p = ρ * R * T)
    (hp0 : p0 = ρ0 * R * T0) (hs : p / ρ ^ γ = p0 / ρ0 ^ γ) :
    p0 / p = (T0 / T) ^ (γ / (γ - 1)) ∧
      p0 / p = (1 + (γ - 1) * M ^ 2 / 2) ^ (γ / (γ - 1)) := by
  have hγ1pos : 0 < γ - 1 := by linarith
  have hγ1 : γ - 1 ≠ 0 := ne_of_gt hγ1pos
  have hγpos : 0 < γ := by linarith
  have hγ0 : γ ≠ 0 := ne_of_gt hγpos
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hT_ne : T ≠ 0 := ne_of_gt hT
  have hcp_pos : 0 < cp := by rw [hcp]; exact div_pos (mul_pos hγpos hR) hγ1pos
  have hcp0 : cp ≠ 0 := ne_of_gt hcp_pos
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ
  have hρ0_ne : ρ0 ≠ 0 := ne_of_gt hρ0
  have hTratio : T0 / T = 1 + (γ - 1) * M ^ 2 / 2 :=
    stagnation_temperature_ratio hγ hR hT hcp ha2 hM hen
  have hcpT0 : 0 < cp * T0 := by
    rw [← hen]
    have h1 : 0 < cp * T := mul_pos hcp_pos hT
    have h2 : 0 ≤ u ^ 2 / 2 := by positivity
    linarith
  have hT0pos : 0 < T0 := pos_of_mul_pos_right hcpT0 (le_of_lt hcp_pos)
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hp0_pos : 0 < p0 := by rw [hp0]; positivity
  have hcp_sub : cp - R = R / (γ - 1) := by
    rw [hcp]; field_simp; ring
  have hRcp : R < cp := sub_pos.mp (by rw [hcp_sub]; exact div_pos hR hγ1pos)
  have hcpR0 : cp - R ≠ 0 := by
    rw [hcp_sub]; exact ne_of_gt (div_pos hR hγ1pos)
  have hγeq : γ = cp / (cp - R) := by
    rw [eq_div_iff hcpR0, hcp_sub, hcp]
    field_simp
  have hv1 : 0 < (1 : ℝ) / ρ := by positivity
  have hv2 : 0 < (1 : ℝ) / ρ0 := by positivity
  have hgas1 : p * (1 / ρ) = R * T := by rw [hp]; field_simp
  have hgas2 : p0 * (1 / ρ0) = R * T0 := by rw [hp0]; field_simp
  have e1 : ((1 : ℝ) / ρ) ^ γ = 1 / ρ ^ γ := by
    rw [Real.div_rpow zero_le_one (le_of_lt hρ), Real.one_rpow]
  have e2 : ((1 : ℝ) / ρ0) ^ γ = 1 / ρ0 ^ γ := by
    rw [Real.div_rpow zero_le_one (le_of_lt hρ0), Real.one_rpow]
  have hadiabat : p * (1 / ρ) ^ γ = p0 * (1 / ρ0) ^ γ := by
    rw [e1, e2, mul_one_div, mul_one_div]; exact hs
  have hpois := EarthScience.poisson_temperature_ratio hp_pos hp0_pos hv1 hv2 hT hR
    hRcp hcp_pos hγeq hgas1 hgas2 hadiabat
  have hRcp_exp : R / cp = (γ - 1) / γ := by
    rw [div_eq_div_iff hcp0 hγ0, hcp]
    field_simp
  rw [hRcp_exp] at hpois
  have hq : 0 < p0 / p := div_pos hp0_pos hp_pos
  have hsq : T0 / T = (p0 / p) ^ ((γ - 1) / γ) := by
    rw [hpois]; field_simp
  have hef : (γ - 1) / γ * (γ / (γ - 1)) = 1 := by field_simp
  have hmain : p0 / p = (T0 / T) ^ (γ / (γ - 1)) := by
    have h := congrArg (fun x => x ^ (γ / (γ - 1))) hsq
    rw [← Real.rpow_mul (le_of_lt hq)] at h
    rw [hef, Real.rpow_one] at h
    exact h.symm
  exact ⟨hmain, by rw [← hTratio]; exact hmain⟩

/-- **Stagnation density.** Under the hypotheses of `stagnation_pressure_ratio`,
`ρ0 / ρ = (T0 / T) ^ (1 / (γ - 1))`, hence `ρ0 / ρ = (1 + (γ - 1) M ^ 2 / 2) ^ (1 / (γ - 1))`. -/
lemma stagnation_density_ratio {γ R T T0 cp a u M ρ ρ0 p p0 : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hT : 0 < T) (hcp : cp = γ * R / (γ - 1)) (ha2 : a ^ 2 = γ * R * T) (hM : M = |u| / a)
    (hen : cp * T + u ^ 2 / 2 = cp * T0) (hρ : 0 < ρ) (hρ0 : 0 < ρ0) (hp : p = ρ * R * T)
    (hp0 : p0 = ρ0 * R * T0) (hs : p / ρ ^ γ = p0 / ρ0 ^ γ) :
    ρ0 / ρ = (T0 / T) ^ (1 / (γ - 1)) ∧
      ρ0 / ρ = (1 + (γ - 1) * M ^ 2 / 2) ^ (1 / (γ - 1)) := by
  have hγ1pos : 0 < γ - 1 := by linarith
  have hγ1 : γ - 1 ≠ 0 := ne_of_gt hγ1pos
  have hγpos : 0 < γ := by linarith
  have hcp_pos : 0 < cp := by rw [hcp]; exact div_pos (mul_pos hγpos hR) hγ1pos
  have hT_ne : T ≠ 0 := ne_of_gt hT
  have hTratio : T0 / T = 1 + (γ - 1) * M ^ 2 / 2 :=
    stagnation_temperature_ratio hγ hR hT hcp ha2 hM hen
  have hpress : p0 / p = (T0 / T) ^ (γ / (γ - 1)) :=
    (stagnation_pressure_ratio hγ hR hT hcp ha2 hM hen hρ hρ0 hp hp0 hs).1
  have hcpT0 : 0 < cp * T0 := by
    rw [← hen]
    have h1 : 0 < cp * T := mul_pos hcp_pos hT
    have h2 : 0 ≤ u ^ 2 / 2 := by positivity
    linarith
  have hT0pos : 0 < T0 := pos_of_mul_pos_right hcpT0 (le_of_lt hcp_pos)
  have hT0_ne : T0 ≠ 0 := ne_of_gt hT0pos
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hRT : R * T ≠ 0 := ne_of_gt (mul_pos hR hT)
  have hRT0 : R * T0 ≠ 0 := ne_of_gt (mul_pos hR hT0pos)
  have hs_pos : 0 < T0 / T := div_pos hT0pos hT
  have hT0T_ne : T0 / T ≠ 0 := ne_of_gt hs_pos
  have hpRT_ne : p / (R * T) ≠ 0 := ne_of_gt (div_pos hp_pos (mul_pos hR hT))
  have hρd : ρ = p / (R * T) := by rw [eq_div_iff hRT, hp]; ring
  have hρ0d : ρ0 = p0 / (R * T0) := by rw [eq_div_iff hRT0, hp0]; ring
  have e : (p0 / (R * T0)) / (p / (R * T)) = (p0 / p) / (T0 / T) := by
    field_simp
  have hexp : γ / (γ - 1) - 1 = 1 / (γ - 1) := by
    field_simp
    ring
  have hmain : ρ0 / ρ = (T0 / T) ^ (1 / (γ - 1)) := by
    rw [hρ0d, hρd, e, hpress]
    nth_rewrite 2 [← Real.rpow_one (T0 / T)]
    rw [← Real.rpow_sub hs_pos, hexp]
  exact ⟨hmain, by rw [← hTratio]; exact hmain⟩

/-! ## D. Boundary cases -/

/-- A moving gas stagnates hotter: under the hypotheses of `stagnation_temperature_ratio`,
`M > 0` gives `T < T0`. -/
lemma temperature_lt_stagnation {γ R T T0 cp a u M : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hT : 0 < T) (hcp : cp = γ * R / (γ - 1)) (ha2 : a ^ 2 = γ * R * T) (hM : M = |u| / a)
    (hen : cp * T + u ^ 2 / 2 = cp * T0) (hMpos : 0 < M) :
    T < T0 := by
  have hγ1pos : 0 < γ - 1 := by linarith
  have hTratio : T0 / T = 1 + (γ - 1) * M ^ 2 / 2 :=
    stagnation_temperature_ratio hγ hR hT hcp ha2 hM hen
  have hM2 : 0 < M ^ 2 := pow_pos hMpos 2
  have hX : 0 < (γ - 1) * M ^ 2 / 2 := by positivity
  have h : 1 < T0 / T := by rw [hTratio]; linarith
  exact (one_lt_div hT).mp h

/-- Static/stagnation boundary: under the hypotheses of `stagnation_pressure_ratio`, at `M = 0`
the stagnation state is the static state, `T0 = T`, `p0 = p` and `ρ0 = ρ`. -/
lemma stagnation_eq_static_of_mach_eq_zero {γ R T T0 cp a u M ρ ρ0 p p0 : ℝ} (hγ : 1 < γ)
    (hR : 0 < R) (hT : 0 < T) (hcp : cp = γ * R / (γ - 1)) (ha2 : a ^ 2 = γ * R * T)
    (hM : M = |u| / a) (hen : cp * T + u ^ 2 / 2 = cp * T0) (hρ : 0 < ρ) (hρ0 : 0 < ρ0)
    (hp : p = ρ * R * T) (hp0 : p0 = ρ0 * R * T0) (hs : p / ρ ^ γ = p0 / ρ0 ^ γ)
    (hM0 : M = 0) :
    T0 = T ∧ p0 = p ∧ ρ0 = ρ := by
  have hγpos : 0 < γ := by linarith
  have hγ1pos : 0 < γ - 1 := by linarith
  have hcp_pos : 0 < cp := by rw [hcp]; exact div_pos (mul_pos hγpos hR) hγ1pos
  have hcp0 : cp ≠ 0 := ne_of_gt hcp_pos
  have ha2pos : 0 < a ^ 2 := by rw [ha2]; positivity
  have ha_ne : a ≠ 0 := fun h => ne_of_gt ha2pos (by rw [h]; norm_num)
  have hu : u = 0 := by
    have h : |u| / a = 0 := by rw [← hM]; exact hM0
    rcases div_eq_zero_iff.mp h with h1 | h2
    · exact abs_eq_zero.mp h1
    · exact absurd h2 ha_ne
  have hT0 : T0 = T := by
    have hen0 := hen
    rw [hu] at hen0
    norm_num at hen0
    rcases hen0 with h | h
    · exact h.symm
    · exact absurd h hcp0
  have hpress := (stagnation_pressure_ratio hγ hR hT hcp ha2 hM hen hρ hρ0 hp hp0 hs).1
  have hdens := (stagnation_density_ratio hγ hR hT hcp ha2 hM hen hρ hρ0 hp hp0 hs).1
  have hTT : T0 / T = 1 := by rw [hT0]; exact div_self (ne_of_gt hT)
  rw [hTT, Real.one_rpow] at hpress
  rw [hTT, Real.one_rpow] at hdens
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hp0eq : p0 = p := (div_eq_one_iff_eq (ne_of_gt hp_pos)).mp hpress
  have hρ0eq : ρ0 = ρ := (div_eq_one_iff_eq (ne_of_gt hρ)).mp hdens
  exact ⟨hT0, hp0eq, hρ0eq⟩

/-- The energy balance alone does not give the isentrope: under the hypotheses of
`stagnation_temperature_ratio` with `M > 0`, and a static state `p = ρ R T` with `ρ > 0`, the
state with pressure `p0 = p`, density `ρ0 = p / (R T0)` and the same `T0` obeys the ideal-gas
law, but its pressure ratio `p0 / p = 1` is below the isentropic `(T0 / T) ^ (γ / (γ - 1))`
(its entropy rises by `cp log (T0 / T) > 0`). -/
lemma stagnation_energy_not_isentropic {γ R T T0 cp a u M ρ p : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hT : 0 < T) (hcp : cp = γ * R / (γ - 1)) (ha2 : a ^ 2 = γ * R * T) (hM : M = |u| / a)
    (hen : cp * T + u ^ 2 / 2 = cp * T0) (hMpos : 0 < M) (hρ : 0 < ρ) (hp : p = ρ * R * T) :
    ∃ ρ0 p0 : ℝ, 0 < ρ0 ∧ p0 = ρ0 * R * T0 ∧ p0 / p < (T0 / T) ^ (γ / (γ - 1)) := by
  have hT0lt : T < T0 :=
    temperature_lt_stagnation hγ hR hT hcp ha2 hM hen hMpos
  have hT0pos : 0 < T0 := by linarith
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hRT0 : 0 < R * T0 := mul_pos hR hT0pos
  have hRT0_ne : R * T0 ≠ 0 := ne_of_gt hRT0
  refine ⟨p / (R * T0), p, ?_, ?_, ?_⟩
  · exact div_pos hp_pos hRT0
  · field_simp
  · rw [div_self hp_ne]
    have hbase : 1 < T0 / T := (one_lt_div hT).mpr hT0lt
    have hγ1pos : 0 < γ - 1 := by linarith
    have hγpos : 0 < γ := by linarith
    have hexp : 0 < γ / (γ - 1) := div_pos hγpos hγ1pos
    exact Real.one_lt_rpow hbase hexp

end FluidDynamics.PerfectGasPorts
