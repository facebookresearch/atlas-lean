/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PhyslibExt.ContinuumMechanics.ControlVolumes

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.PoissonAdiabat

/-!
# Perfect-gas ports: the stagnation state adapter and the isentropic mass flux

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

Through the isentrope, the static state at the Mach number `M` carries the mass flux per unit area
`ρ |u| = G(M) = p0 √(γ / (R T0)) M (1 + (γ - 1) M ^ 2 / 2) ^ (-(γ + 1) / (2 (γ - 1)))` (real
power). Its derivative `G'(M) = p0 √(γ / (R T0)) (1 - M ^ 2) X ^ (-(γ + 1) / (2 (γ - 1)) - 1)`,
with `X = 1 + (γ - 1) M ^ 2 / 2 ≥ 1`, is positive for `0 < M < 1` and negative for `M > 1`, so `G`
increases strictly on `(0, 1)`, decreases strictly on `(1, ∞)`, and the sonic value `G(1)` is its
unique maximum. A section of area `A` at `M > 0` and a sonic section of area `A*` that carry the
same mass flow at the same stagnation state, `G(M) A = G(1) A*`, therefore have
`A / A* = G(1) / G(M) ≥ 1`. At `M = 0` the flux vanishes and the quotient `G(1) / G(0)` is Lean's
`x / 0 = 0`, so the area ratio needs `M > 0`. Both branches occur, and strict monotonicity on each
side makes the inverse Mach number of an area ratio unique only once a branch is selected.

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
- `FluidDynamics.PerfectGasPorts.isentropicMassFlux`,
  `FluidDynamics.PerfectGasPorts.massFlux_eq_isentropicMassFlux`: the flux `G(M)`, and
  `ρ |u| = G(M)` on the isentrope.
- `FluidDynamics.PerfectGasPorts.hasDerivAt_isentropicMassFlux`: the derivative of `G`.
- `FluidDynamics.PerfectGasPorts.isentropicMassFlux_strictMonoOn`,
  `FluidDynamics.PerfectGasPorts.isentropicMassFlux_strictAntiOn`,
  `FluidDynamics.PerfectGasPorts.isentropicMassFlux_lt_sonic`: monotonicity and the unique
  maximum at `M = 1`.
- `FluidDynamics.PerfectGasPorts.area_ratio_eq_and_one_le`: `A / A* = G(1) / G(M) ≥ 1`.
- `FluidDynamics.PerfectGasPorts.isentropicMassFlux_zero`: zero flux and no area ratio at
  `M = 0`.

## iii. Table of contents

- A. Port enthalpy of a calorically perfect gas
- B. Stagnation temperature
- C. Stagnation pressure and density through the isentrope
- D. Boundary cases
- E. The isentropic mass flux
- F. Monotonicity and the sonic maximum
- G. The critical-area ratio

## iv. References

- J. D. Anderson, *Modern Compressible Flow*, 3rd ed., McGraw-Hill, 2003, ch. 3: the total
  temperature `T0 / T = 1 + (γ - 1) M ^ 2 / 2` from the adiabatic energy equation, and the total
  pressure and density ratios of an isentropic deceleration; ch. 5: the area-Mach-number relation
  and choked mass flow in quasi-one-dimensional isentropic flow.
- H. W. Liepmann and A. Roshko, *Elements of Gasdynamics*, Wiley, 1957, ch. 2: the mass flux per
  unit area and its maximum at `M = 1`.
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

/-! ## E. The isentropic mass flux -/

/-- The isentropic mass flux per unit area of a perfect gas with stagnation pressure `p0`,
stagnation temperature `T0`, specific gas constant `R` and heat-capacity ratio `γ`, at the Mach
number `M`: `G(M) = p0 √(γ / (R T0)) M (1 + (γ - 1) M ^ 2 / 2) ^ (-(γ + 1) / (2 (γ - 1)))`, with
a real power. -/
noncomputable def isentropicMassFlux (p0 T0 R γ M : ℝ) : ℝ :=
  p0 * Real.sqrt (γ / (R * T0)) * M * (1 + (γ - 1) * M ^ 2 / 2) ^ (-(γ + 1) / (2 * (γ - 1)))

/-- **The flux of the isentropic state.** Under the hypotheses of `stagnation_pressure_ratio`
(stagnation energy balance, ideal-gas law at both states, declared isentropic connection) and a
positive sound speed `a`, the mass flux `ρ |u|` of the static state is `G(M)` at its stagnation
pressure and temperature. -/
lemma massFlux_eq_isentropicMassFlux {γ R T T0 cp a u M ρ ρ0 p p0 : ℝ} (hγ : 1 < γ)
    (hR : 0 < R) (hT : 0 < T) (hcp : cp = γ * R / (γ - 1)) (ha : 0 < a)
    (ha2 : a ^ 2 = γ * R * T) (hM : M = |u| / a) (hen : cp * T + u ^ 2 / 2 = cp * T0)
    (hρ : 0 < ρ) (hρ0 : 0 < ρ0) (hp : p = ρ * R * T) (hp0 : p0 = ρ0 * R * T0)
    (hs : p / ρ ^ γ = p0 / ρ0 ^ γ) :
    ρ * |u| = isentropicMassFlux p0 T0 R γ M := by
  have hγ1pos : 0 < γ - 1 := by linarith
  have hγ1 : γ - 1 ≠ 0 := ne_of_gt hγ1pos
  have hγpos : 0 < γ := by linarith
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hTne : T ≠ 0 := ne_of_gt hT
  have hane : a ≠ 0 := ne_of_gt ha
  have hcp_pos : 0 < cp := by rw [hcp]; exact div_pos (mul_pos hγpos hR) hγ1pos
  have hcpT0 : 0 < cp * T0 := by
    rw [← hen]
    have h1 : 0 < cp * T := mul_pos hcp_pos hT
    have h2 : 0 ≤ u ^ 2 / 2 := by positivity
    linarith
  have hT0pos : 0 < T0 := pos_of_mul_pos_right hcpT0 (le_of_lt hcp_pos)
  have hT0ne : T0 ≠ 0 := ne_of_gt hT0pos
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hp0_pos : 0 < p0 := by rw [hp0]; positivity
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hRTne : R * T ≠ 0 := mul_ne_zero hR0 hTne
  have hXge : (1:ℝ) ≤ 1 + (γ - 1) * M ^ 2 / 2 := by
    have hnn : (0:ℝ) ≤ (γ - 1) * M ^ 2 / 2 := by positivity
    linarith
  have hXpos : (0:ℝ) < 1 + (γ - 1) * M ^ 2 / 2 := lt_of_lt_of_le zero_lt_one hXge
  have hTratio : T0 / T = 1 + (γ - 1) * M ^ 2 / 2 :=
    stagnation_temperature_ratio hγ hR hT hcp ha2 hM hen
  have hpratio := stagnation_pressure_ratio hγ hR hT hcp ha2 hM hen hρ hρ0 hp hp0 hs
  have hpratio2 : p0 / p = (1 + (γ - 1) * M ^ 2 / 2) ^ (γ / (γ - 1)) := hpratio.2
  have hu : |u| = M * a := by
    rw [hM]
    field_simp
  have ha_sqrt : a = Real.sqrt (γ * R * T) := by
    have h : Real.sqrt (a ^ 2) = a := Real.sqrt_sq (le_of_lt ha)
    rw [ha2] at h
    exact h.symm
  have hρeq : ρ = p / (R * T) := by
    rw [hp]
    field_simp
  have h_sqrt1 : Real.sqrt (γ * R * T) / (R * T) = Real.sqrt (γ / (R * T)) := by
    have hRT : 0 < R * T := mul_pos hR hT
    have hγnn : (0:ℝ) ≤ γ := le_of_lt hγpos
    have hRTnn : (0:ℝ) ≤ R * T := le_of_lt hRT
    have h1 : Real.sqrt (γ * R * T) = Real.sqrt γ * Real.sqrt (R * T) := by
      rw [mul_assoc]
      exact Real.sqrt_mul hγnn _
    have h2 : Real.sqrt (γ / (R * T)) = Real.sqrt γ / Real.sqrt (R * T) :=
      Real.sqrt_div hγnn _
    have hsq : Real.sqrt (R * T) ^ 2 = R * T := Real.sq_sqrt hRTnn
    have hsqrt_ne : Real.sqrt (R * T) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hRT)
    rw [h1, h2]
    field_simp
    exact hsq
  have h_flux1 : ρ * |u| = p * M * Real.sqrt (γ / (R * T)) := by
    rw [hρeq, hu, ha_sqrt]
    have heq : (p / (R * T)) * (M * Real.sqrt (γ * R * T)) =
        p * M * (Real.sqrt (γ * R * T) / (R * T)) := by ring
    rw [heq, h_sqrt1]
  have h_sqrt2 : Real.sqrt (γ / (R * T)) =
      Real.sqrt (γ / (R * T0)) * Real.sqrt (1 + (γ - 1) * M ^ 2 / 2) := by
    have harg1 : (0:ℝ) ≤ γ / (R * T0) :=
      le_of_lt (div_pos hγpos (mul_pos hR hT0pos))
    have heq : γ / (R * T) = (γ / (R * T0)) * (1 + (γ - 1) * M ^ 2 / 2) := by
      rw [← hTratio]
      field_simp
    rw [heq]
    exact Real.sqrt_mul harg1 _
  have hXg_pos : (0:ℝ) < (1 + (γ - 1) * M ^ 2 / 2) ^ (γ / (γ - 1)) :=
    Real.rpow_pos_of_pos hXpos _
  have hXg_ne : (1 + (γ - 1) * M ^ 2 / 2) ^ (γ / (γ - 1)) ≠ 0 := ne_of_gt hXg_pos
  have h_p : p = p0 / (1 + (γ - 1) * M ^ 2 / 2) ^ (γ / (γ - 1)) := by
    rw [eq_div_iff hXg_ne]
    have h1 : p0 / p = (1 + (γ - 1) * M ^ 2 / 2) ^ (γ / (γ - 1)) := hpratio2
    rw [div_eq_iff hp_ne] at h1
    linear_combination -h1
  have h_p2 : p = p0 * (1 + (γ - 1) * M ^ 2 / 2) ^ (-(γ / (γ - 1))) := by
    rw [h_p, div_eq_mul_inv]
    congr 1
    exact (Real.rpow_neg (le_of_lt hXpos) _).symm
  have hexp : (1 / 2 - γ / (γ - 1) : ℝ) = (-(γ + 1) / (2 * (γ - 1)) : ℝ) := by
    field_simp
    ring
  have h_rpow : (1 + (γ - 1) * M ^ 2 / 2) ^ (-(γ / (γ - 1))) *
      (1 + (γ - 1) * M ^ 2 / 2) ^ ((1 / 2 : ℝ)) =
      (1 + (γ - 1) * M ^ 2 / 2) ^ (-(γ + 1) / (2 * (γ - 1))) := by
    rw [← Real.rpow_add hXpos]
    congr 1
    have h : (-(γ / (γ - 1)) + 1 / 2 : ℝ) = 1 / 2 - γ / (γ - 1) := by ring
    rw [h, hexp]
  rw [h_flux1, h_p2, h_sqrt2, Real.sqrt_eq_rpow (1 + (γ - 1) * M ^ 2 / 2)]
  unfold isentropicMassFlux
  linear_combination (p0 * Real.sqrt (γ / (R * T0)) * M) * h_rpow

/-- **Derivative of the flux.** For `γ > 1`, at every `M`,
`G'(M) = p0 √(γ / (R T0)) (1 - M ^ 2) (1 + (γ - 1) M ^ 2 / 2) ^ (-(γ + 1) / (2 (γ - 1)) - 1)`.
The base `1 + (γ - 1) M ^ 2 / 2` is at least `1`, so the real power is differentiable. -/
lemma hasDerivAt_isentropicMassFlux {γ : ℝ} (hγ : 1 < γ) (p0 T0 R M : ℝ) :
    HasDerivAt (isentropicMassFlux p0 T0 R γ)
      (p0 * Real.sqrt (γ / (R * T0)) * (1 - M ^ 2) *
        (1 + (γ - 1) * M ^ 2 / 2) ^ (-(γ + 1) / (2 * (γ - 1)) - 1)) M := by
  have hγ1pos : 0 < γ - 1 := by linarith
  have hγ1 : γ - 1 ≠ 0 := ne_of_gt hγ1pos
  have hXge : (1:ℝ) ≤ 1 + (γ - 1) * M ^ 2 / 2 := by
    have hnn : (0:ℝ) ≤ (γ - 1) * M ^ 2 / 2 := by positivity
    linarith
  have hXpos : (0:ℝ) < 1 + (γ - 1) * M ^ 2 / 2 := lt_of_lt_of_le zero_lt_one hXge
  have hXne : (1 + (γ - 1) * M ^ 2 / 2 : ℝ) ≠ 0 := ne_of_gt hXpos
  have hpow : HasDerivAt (fun M : ℝ => M ^ 2) (2 * M) M := by
    have h := hasDerivAt_pow 2 M
    simpa using h
  have hmul : HasDerivAt (fun M : ℝ => (γ - 1) * M ^ 2) ((γ - 1) * (2 * M)) M :=
    HasDerivAt.const_mul (γ - 1) hpow
  have hdiv : HasDerivAt (fun M : ℝ => (γ - 1) * M ^ 2 / 2) (((γ - 1) * (2 * M)) / 2) M :=
    HasDerivAt.div_const hmul 2
  have hX : HasDerivAt (fun M : ℝ => 1 + (γ - 1) * M ^ 2 / 2) ((γ - 1) * M) M := by
    have hadd : HasDerivAt (fun M : ℝ => 1 + (γ - 1) * M ^ 2 / 2) (((γ - 1) * (2 * M)) / 2) M :=
      HasDerivAt.const_add 1 hdiv
    convert hadd using 1
    ring
  set e : ℝ := -(γ + 1) / (2 * (γ - 1)) with he
  have hXpow : HasDerivAt (fun M : ℝ => (1 + (γ - 1) * M ^ 2 / 2) ^ e)
      (((γ - 1) * M) * e * (1 + (γ - 1) * M ^ 2 / 2) ^ (e - 1)) M :=
    HasDerivAt.rpow_const hX (Or.inl hXne)
  have hCM : HasDerivAt (fun M : ℝ => p0 * Real.sqrt (γ / (R * T0)) * M)
      (p0 * Real.sqrt (γ / (R * T0))) M := by
    have h := hasDerivAt_const_mul (p0 * Real.sqrt (γ / (R * T0))) (x := M)
    simpa using h
  have hG : HasDerivAt (fun M : ℝ => (p0 * Real.sqrt (γ / (R * T0)) * M) *
      (1 + (γ - 1) * M ^ 2 / 2) ^ e)
      ((p0 * Real.sqrt (γ / (R * T0))) * (1 + (γ - 1) * M ^ 2 / 2) ^ e +
        (p0 * Real.sqrt (γ / (R * T0)) * M) * (((γ - 1) * M) * e *
          (1 + (γ - 1) * M ^ 2 / 2) ^ (e - 1))) M := hCM.mul hXpow
  have hXpow_eq : (1 + (γ - 1) * M ^ 2 / 2 : ℝ) ^ e =
      (1 + (γ - 1) * M ^ 2 / 2) * (1 + (γ - 1) * M ^ 2 / 2) ^ (e - 1) := by
    have he1 : e = (e - 1) + 1 := by ring
    conv_lhs => rw [he1]
    rw [Real.rpow_add hXpos, Real.rpow_one]
    ring
  have heγ : e * (γ - 1) = -(γ + 1) / 2 := by
    rw [he]
    field_simp
  have hkey : (1 + (γ - 1) * M ^ 2 / 2 : ℝ) + e * (γ - 1) * M ^ 2 = 1 - M ^ 2 := by
    have h1 : e * (γ - 1) * M ^ 2 = (-(γ + 1) / 2) * M ^ 2 := by rw [← heγ]
    rw [h1]
    ring
  have hderiv : (p0 * Real.sqrt (γ / (R * T0))) * (1 + (γ - 1) * M ^ 2 / 2) ^ e +
        (p0 * Real.sqrt (γ / (R * T0)) * M) * (((γ - 1) * M) * e *
          (1 + (γ - 1) * M ^ 2 / 2) ^ (e - 1)) =
      p0 * Real.sqrt (γ / (R * T0)) * (1 - M ^ 2) *
        (1 + (γ - 1) * M ^ 2 / 2) ^ (e - 1) := by
    rw [hXpow_eq]
    have h2 : (p0 * Real.sqrt (γ / (R * T0)) * M) * (((γ - 1) * M) * e *
        (1 + (γ - 1) * M ^ 2 / 2) ^ (e - 1)) =
        p0 * Real.sqrt (γ / (R * T0)) * (e * (γ - 1) * M ^ 2) *
          (1 + (γ - 1) * M ^ 2 / 2) ^ (e - 1) := by ring
    rw [h2]
    linear_combination (p0 * Real.sqrt (γ / (R * T0)) *
      (1 + (γ - 1) * M ^ 2 / 2) ^ (e - 1)) * hkey
  rw [hderiv] at hG
  have hfun : (fun M : ℝ => (p0 * Real.sqrt (γ / (R * T0)) * M) *
      (1 + (γ - 1) * M ^ 2 / 2) ^ e) = isentropicMassFlux p0 T0 R γ := by
    unfold isentropicMassFlux
    simp only [he]
  rw [hfun] at hG
  exact hG

/-! ## F. Monotonicity and the sonic maximum -/

private lemma X_ge_one {γ M : ℝ} (hγ : 1 < γ) : (1:ℝ) ≤ 1 + (γ - 1) * M ^ 2 / 2 := by
  have hnn : (0:ℝ) ≤ (γ - 1) * M ^ 2 / 2 := by
    have hγ1 : (0:ℝ) < γ - 1 := by linarith
    positivity
  linarith

private lemma X_pos {γ M : ℝ} (hγ : 1 < γ) : (0:ℝ) < 1 + (γ - 1) * M ^ 2 / 2 :=
  lt_of_lt_of_le zero_lt_one (X_ge_one hγ)

private lemma C_pos {p0 T0 R γ : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0) (hR : 0 < R)
    (hγ : 1 < γ) : 0 < p0 * Real.sqrt (γ / (R * T0)) := by
  have hγpos : 0 < γ := by linarith
  have hRT : 0 < R * T0 := mul_pos hR hT0
  exact mul_pos hp0 (Real.sqrt_pos.mpr (div_pos hγpos hRT))

private lemma Xpow_pos {γ M e : ℝ} (hγ : 1 < γ) :
    0 < (1 + (γ - 1) * M ^ 2 / 2) ^ e :=
  Real.rpow_pos_of_pos (X_pos hγ) e

private lemma G_continuous {p0 T0 R γ : ℝ} (hγ : 1 < γ) :
    Continuous (isentropicMassFlux p0 T0 R γ) := by
  have hdiff : Differentiable ℝ (isentropicMassFlux p0 T0 R γ) :=
    fun x => (hasDerivAt_isentropicMassFlux hγ p0 T0 R x).differentiableAt
  exact hdiff.continuous

private lemma G_deriv {p0 T0 R γ M : ℝ} (hγ : 1 < γ) :
    deriv (isentropicMassFlux p0 T0 R γ) M =
      p0 * Real.sqrt (γ / (R * T0)) * (1 - M ^ 2) *
        (1 + (γ - 1) * M ^ 2 / 2) ^ (-(γ + 1) / (2 * (γ - 1)) - 1) :=
  (hasDerivAt_isentropicMassFlux hγ p0 T0 R M).deriv

private lemma G_strictMono_Icc {p0 T0 R γ : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0)
    (hR : 0 < R) (hγ : 1 < γ) :
    StrictMonoOn (isentropicMassFlux p0 T0 R γ) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) (G_continuous hγ).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [G_deriv hγ]
  have hC := C_pos hp0 hT0 hR hγ
  have h1 : (0:ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hX := Xpow_pos (M := x) (e := -(γ + 1) / (2 * (γ - 1)) - 1) hγ
  exact mul_pos (mul_pos hC h1) hX

private lemma G_strictAnti_Ici {p0 T0 R γ : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0)
    (hR : 0 < R) (hγ : 1 < γ) :
    StrictAntiOn (isentropicMassFlux p0 T0 R γ) (Set.Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1) (G_continuous hγ).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have hx' : (1:ℝ) < x := hx
  rw [G_deriv hγ]
  have hC := C_pos hp0 hT0 hR hγ
  have h1 : (1:ℝ) - x ^ 2 < 0 := by nlinarith [hx']
  have hX := Xpow_pos (M := x) (e := -(γ + 1) / (2 * (γ - 1)) - 1) hγ
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hC h1) hX

/-- **Subsonic increase.** For positive `p0`, `T0`, `R` and `γ > 1`, the flux increases strictly
on `(0, 1)`. -/
lemma isentropicMassFlux_strictMonoOn {p0 T0 R γ : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0)
    (hR : 0 < R) (hγ : 1 < γ) :
    StrictMonoOn (isentropicMassFlux p0 T0 R γ) (Set.Ioo 0 1) := by
  have h := G_strictMono_Icc hp0 hT0 hR hγ
  intro x hx y hy hxy
  exact h ⟨le_of_lt hx.1, le_of_lt hx.2⟩ ⟨le_of_lt hy.1, le_of_lt hy.2⟩ hxy

/-- **Supersonic decrease.** For positive `p0`, `T0`, `R` and `γ > 1`, the flux decreases
strictly on `(1, ∞)`. -/
lemma isentropicMassFlux_strictAntiOn {p0 T0 R γ : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0)
    (hR : 0 < R) (hγ : 1 < γ) :
    StrictAntiOn (isentropicMassFlux p0 T0 R γ) (Set.Ioi 1) := by
  have h := G_strictAnti_Ici hp0 hT0 hR hγ
  intro x hx y hy hxy
  exact h (le_of_lt hx) (le_of_lt hy) hxy

private lemma G_pos_of_pos {p0 T0 R γ M : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0)
    (hR : 0 < R) (hγ : 1 < γ) (hM : 0 < M) :
    0 < isentropicMassFlux p0 T0 R γ M := by
  have hC := C_pos hp0 hT0 hR hγ
  have hX := Xpow_pos (M := M) (e := -(γ + 1) / (2 * (γ - 1))) hγ
  unfold isentropicMassFlux
  exact mul_pos (mul_pos hC hM) hX

private lemma G_neg_of_neg {p0 T0 R γ M : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0)
    (hR : 0 < R) (hγ : 1 < γ) (hM : M < 0) :
    isentropicMassFlux p0 T0 R γ M < 0 := by
  have hC := C_pos hp0 hT0 hR hγ
  have hX := Xpow_pos (M := M) (e := -(γ + 1) / (2 * (γ - 1))) hγ
  unfold isentropicMassFlux
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hC hM) hX

/-- **The sonic maximum is unique.** For positive `p0`, `T0`, `R` and `γ > 1`, every `M ≠ 1` has
`G(M) < G(1)`; for `M < 0`, which is not a Mach number, `G(M) < 0`. -/
lemma isentropicMassFlux_lt_sonic {p0 T0 R γ M : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0)
    (hR : 0 < R) (hγ : 1 < γ) (hM : M ≠ 1) :
    isentropicMassFlux p0 T0 R γ M < isentropicMassFlux p0 T0 R γ 1 := by
  by_cases hM0 : M < 0
  · have hGM := G_neg_of_neg hp0 hT0 hR hγ hM0
    have hG1 := G_pos_of_pos hp0 hT0 hR hγ (M := 1) zero_lt_one
    linarith
  · by_cases hM0' : M = 0
    · subst hM0'
      have h0 : isentropicMassFlux p0 T0 R γ 0 = 0 := by simp [isentropicMassFlux]
      have hG1 := G_pos_of_pos hp0 hT0 hR hγ (M := 1) zero_lt_one
      rw [h0]
      exact hG1
    · have hMpos : 0 < M := lt_of_le_of_ne (le_of_not_gt hM0) (Ne.symm hM0')
      by_cases hM1 : M < 1
      · have hmono := G_strictMono_Icc hp0 hT0 hR hγ
        exact hmono ⟨le_of_lt hMpos, le_of_lt hM1⟩ ⟨zero_le_one, le_refl 1⟩ hM1
      · have hMgt : 1 < M := lt_of_le_of_ne (le_of_not_gt hM1) (Ne.symm hM)
        have hanti := G_strictAnti_Ici hp0 hT0 hR hγ
        exact hanti (le_refl 1) (le_of_lt hMgt) hMgt

/-! ## G. The critical-area ratio -/

/-- **Critical-area ratio.** For positive `p0`, `T0`, `R`, `γ > 1` and `M > 0`, a section of
area `A` at Mach number `M` and a sonic section of positive area `Astar` that carry the same mass
flow at the same stagnation state, `G(M) A = G(1) Astar`, have `A / Astar = G(1) / G(M) ≥ 1`. -/
lemma area_ratio_eq_and_one_le {p0 T0 R γ M A Astar : ℝ} (hp0 : 0 < p0) (hT0 : 0 < T0)
    (hR : 0 < R) (hγ : 1 < γ) (hM : 0 < M) (hAstar : 0 < Astar)
    (hmass : isentropicMassFlux p0 T0 R γ M * A = isentropicMassFlux p0 T0 R γ 1 * Astar) :
    A / Astar = isentropicMassFlux p0 T0 R γ 1 / isentropicMassFlux p0 T0 R γ M ∧
      1 ≤ A / Astar := by
  have hGM := G_pos_of_pos hp0 hT0 hR hγ hM
  have hAstarne : Astar ≠ 0 := ne_of_gt hAstar
  have hGMne : isentropicMassFlux p0 T0 R γ M ≠ 0 := ne_of_gt hGM
  have heq : A / Astar = isentropicMassFlux p0 T0 R γ 1 / isentropicMassFlux p0 T0 R γ M := by
    rw [div_eq_div_iff hAstarne hGMne]
    linear_combination hmass
  have hle : isentropicMassFlux p0 T0 R γ M ≤ isentropicMassFlux p0 T0 R γ 1 := by
    by_cases h : M = 1
    · subst h
      exact le_refl _
    · exact le_of_lt (isentropicMassFlux_lt_sonic hp0 hT0 hR hγ h)
  have h1 : (1:ℝ) ≤ isentropicMassFlux p0 T0 R γ 1 / isentropicMassFlux p0 T0 R γ M :=
    (one_le_div hGM).mpr hle
  exact ⟨heq, by rw [heq]; exact h1⟩

/-- **No area ratio at rest.** At `M = 0` the flux vanishes, and the area-ratio quotient
`G(1) / G(0)` is Lean's `x / 0 = 0`, which violates `≥ 1`: the area-ratio division needs
`M > 0`. -/
lemma isentropicMassFlux_zero (p0 T0 R γ : ℝ) :
    isentropicMassFlux p0 T0 R γ 0 = 0 ∧
      ¬ 1 ≤ isentropicMassFlux p0 T0 R γ 1 / isentropicMassFlux p0 T0 R γ 0 := by
  have h0 : isentropicMassFlux p0 T0 R γ 0 = 0 := by
    simp [isentropicMassFlux]
  exact ⟨h0, by rw [h0, div_zero]; norm_num⟩

end FluidDynamics.PerfectGasPorts
