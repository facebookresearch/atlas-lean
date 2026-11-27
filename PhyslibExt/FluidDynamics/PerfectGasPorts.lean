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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.PoissonAdiabat

/-!
# Perfect-gas ports: stagnation state, isentropic mass flux, area-velocity relation, normal shocks

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

In steady quasi-one-dimensional flow along the duct coordinate `x`, with area `A(x)`, density
`ρ(x)` and speed `u(x)`, let the ideal-gas law, the declared isentropic connection to one
stagnation state, the stagnation energy balance and the mass flow `ρ u A = ṁ` hold near a station
`x₀`. Differentiating the stagnation density ratio and the energy balance gives
`ρ' / ρ = -M ^ 2 u' / u`, and differentiating the mass flow gives `ρ' / ρ + u' / u + A' / A = 0`;
together they give the area-velocity relation `A' / A = (M ^ 2 - 1) u' / u` for positive `A`,
`ρ`, `u`. So a sonic station has stationary area, `A' = 0`: a necessary condition for a throat,
not an area minimum, which these results do not assert. The converse needs more than stationary
area: `u' ≠ 0` at the station gives `M = 1` through the relation, and so does a mass flow selected
at the choked value `ṁ = G(1) A` of the sonic maximum, without any derivative. Stationary area
alone does not, even at a throat: a subsonic venturi has a strict area minimum, hence `A' = 0`,
with `u' = 0` and `M < 1`. Both cases are constructed in the test module.

A steady normal shock joins an upstream state `(ρ1, u1, p1, T1)` to a downstream state
`(ρ2, u2, p2, T2)` of the same gas: both obey `p = ρ R T`, and the jump conditions conserve the
mass flux `ρ u`, the momentum flux `p + ρ u ^ 2` and the total enthalpy `cp T + u ^ 2 / 2`
(`IsNormalShockJump`). These balance laws are declared model inputs, not derived. With the
upstream sound speed `a1 ^ 2 = γ R T1`, Mach number `M1 = |u1| / a1` and `m = M1 ^ 2`, the trivial
branch, the downstream state equal to the upstream one, always solves them, and for `u1 > 0` so
does the distinct branch `ρ2 / ρ1 = (γ + 1) m / ((γ - 1) m + 2)`,
`p2 / p1 = (2 γ m - (γ - 1)) / (γ + 1)`, with the temperature ratio their quotient. The distinct
root is a positive state exactly for `m > (γ - 1) / (2 γ)`, where its pressure turns positive.
Every solution with positive densities and temperatures is on one of the two branches, on the
distinct one only above that threshold, and the two coincide at `m = 1`. The classification is
about positive states, not every real root: the entropy condition `m ≥ 1`, which selects the
compression shocks, is not part of it.

Sections L-M apply that condition. The entropy change per unit mass of a calorically perfect gas
is `specificEntropyChange cv R T1 v1 T2 v2 = cv log (T2 / T1) + R log (v2 / v1)`, with the specific
heat at constant volume `cv`, the specific gas constant `R` and the specific volumes `v = 1 / ρ`.
For `cv = R / (γ - 1)` and `p = ρ R T` it takes the `(T, p)` form
`cp log (T2 / T1) - R log (p2 / p1)`; on the distinct branch, where `T2 / T1 = P / r` for its
pressure and density ratios `P` and `r`, it is `R` times
`Δs / R = log P / (γ - 1) - γ log r / (γ - 1)` (`shockEntropyJump`).
Above the threshold this jump has the derivative
`2 γ (m - 1) ^ 2 / (m ((γ - 1) m + 2) (2 γ m - γ + 1))` in `m` and vanishes at `m = 1`, so across
a nontrivial jump with `M1 > 0` the entropy rises exactly for `M1 > 1` and falls on the expansion
branch `(γ - 1) / (2 γ) < M1 ^ 2 < 1`. Below the threshold the jump is a junk value of
`Real.log` at a nonpositive ratio and no lemma reads it. The total enthalpy is conserved, so the
stagnation temperatures agree, and with each stagnation state joined to its static state by the
declared isentropic connection, `p02 / p01 = exp (-Δs / R)`: the total pressure falls across the
compression shock and rises across the expansion root, which solves the jump conditions but is
entropy-inadmissible.

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
- `FluidDynamics.PerfectGasPorts.isentropic_density_derivative`,
  `FluidDynamics.PerfectGasPorts.mass_flow_derivative`: `ρ' / ρ = -M ^ 2 u' / u` and
  `ρ' / ρ + u' / u + A' / A = 0`.
- `FluidDynamics.PerfectGasPorts.area_velocity_relation`: `A' / A = (M ^ 2 - 1) u' / u`.
- `FluidDynamics.PerfectGasPorts.area_deriv_eq_zero_of_mach_eq_one`: a sonic station has
  stationary area, `A' = 0`.
- `FluidDynamics.PerfectGasPorts.mach_eq_one_of_area_deriv_eq_zero`,
  `FluidDynamics.PerfectGasPorts.mach_eq_one_of_choked`: a station of stationary area with
  `u' ≠ 0`, or a station at the choked mass flow, is sonic.
- `FluidDynamics.PerfectGasPorts.IsNormalShockJump`: the normal-shock jump conditions.
- `FluidDynamics.PerfectGasPorts.isNormalShockJump_self`,
  `FluidDynamics.PerfectGasPorts.isNormalShockJump_distinct`: the trivial and the distinct branch.
- `FluidDynamics.PerfectGasPorts.normalShock_classification`: every solution with positive
  densities and temperatures is on one of the two branches, the distinct one only above
  `(γ - 1) / (2 γ)`.
- `FluidDynamics.PerfectGasPorts.isNormalShockJump_distinct_pos_iff`: the distinct root is a
  positive state exactly above `(γ - 1) / (2 γ)`.
- `FluidDynamics.PerfectGasPorts.shockRatio_eq_one_iff`: the two roots coincide exactly at
  `m = 1`.
- `FluidDynamics.PerfectGasPorts.specificEntropyChange`,
  `FluidDynamics.PerfectGasPorts.specificEntropyChange_perfectGas`: the entropy change per unit
  mass and its `(T, p)` form.
- `FluidDynamics.PerfectGasPorts.shockEntropyJump`,
  `FluidDynamics.PerfectGasPorts.shockEntropyJump_one`,
  `FluidDynamics.PerfectGasPorts.hasDerivAt_shockEntropyJump`,
  `FluidDynamics.PerfectGasPorts.shockEntropyJump_pos_iff`: the entropy jump of the distinct
  branch, zero at `m = 1`, its derivative and its sign.
- `FluidDynamics.PerfectGasPorts.normalShock_entropyChange`,
  `FluidDynamics.PerfectGasPorts.normalShock_entropy_pos_iff`: the entropy change of a nontrivial
  positive-state jump, positive exactly for `M1 > 1`.
- `FluidDynamics.PerfectGasPorts.normalShock_stagnationPressure_ratio`,
  `FluidDynamics.PerfectGasPorts.normalShock_totalPressure_selection`: `T02 = T01` and
  `p02 / p01 = exp (-Δs / R)`; the total pressure falls for `M1 > 1` and rises on the
  entropy-inadmissible expansion branch.

## iii. Table of contents

- A. Port enthalpy of a calorically perfect gas
- B. Stagnation temperature
- C. Stagnation pressure and density through the isentrope
- D. Boundary cases
- E. The isentropic mass flux
- F. Monotonicity and the sonic maximum
- G. The critical-area ratio
- H. The differentiated isentrope and mass conservation
- I. The area-velocity relation and stationary area at a sonic station
- J. Normal-shock jump conditions and branch ratios
- K. The two normal-shock branches
- L. Specific entropy change in `(T, p)` form and on the distinct branch
- M. Selection of the compression branch

## iv. References

- J. D. Anderson, *Modern Compressible Flow*, 3rd ed., McGraw-Hill, 2003, ch. 3: the total
  temperature `T0 / T = 1 + (γ - 1) M ^ 2 / 2` from the adiabatic energy equation, the total
  pressure and density ratios of an isentropic deceleration, the normal-shock ratios
  `ρ2 / ρ1`, `p2 / p1`, `T2 / T1` as functions of `M1`, the entropy change
  `s2 - s1 = cp ln (T2 / T1) - R ln (p2 / p1)` across the shock, which selects `M1 > 1`, and
  `p02 / p01 = exp (-(s2 - s1) / R)` at unchanged total temperature; ch. 5: the area-velocity and
  area-Mach-number relations, sonic flow at a minimum-area section and choked mass flow in
  quasi-one-dimensional isentropic flow.
- H. W. Liepmann and A. Roshko, *Elements of Gasdynamics*, Wiley, 1957, ch. 2: flow in a stream
  tube of varying area, the mass flux per unit area and its maximum at `M = 1`.
- A. H. Shapiro, *The Dynamics and Thermodynamics of Compressible Fluid Flow*, vol. 1, Ronald
  Press, 1953, ch. 5: the trivial and the shock solution of the normal-shock jump conditions, and
  the rarefaction shock, an algebraic solution that the second law excludes.
- NACA Report 1135, *Equations, Tables, and Charts for Compressible Flow*, 1953: the
  normal-shock table (`M1 = 2`, `γ = 1.4`: `p2 / p1 = 4.5`, `ρ2 / ρ1 = 2.667`,
  `T2 / T1 = 1.688`, `p02 / p01 = 0.7209`).
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

/-! ## H. The differentiated isentrope and mass conservation -/

open scoped Topology

/-- **Differentiated isentrope.** Near the station `x₀` let the temperature and density be
positive and the ideal-gas law, the declared isentropic connection to the stagnation state and the
stagnation energy balance hold, with `γ > 1`, `R > 0`, `cp = γ R / (γ - 1)`, `ρ0 > 0` and
`p0 = ρ0 R T0`. At the station let `u > 0`, `a ^ 2 = γ R T` and `M = |u| / a`. If `ρ` and `u`
have the derivatives `ρ'` and `u'` there, then `ρ' / ρ = -M ^ 2 u' / u`. -/
lemma isentropic_density_derivative {γ R cp T0 ρ0 p0 a M x₀ ρ' u' : ℝ} {ρ u T p : ℝ → ℝ}
    (hγ : 1 < γ) (hR : 0 < R) (hcp : cp = γ * R / (γ - 1)) (hρ0 : 0 < ρ0)
    (hp0 : p0 = ρ0 * R * T0) (hT : ∀ᶠ x in 𝓝 x₀, 0 < T x) (hρ : ∀ᶠ x in 𝓝 x₀, 0 < ρ x)
    (hp : ∀ᶠ x in 𝓝 x₀, p x = ρ x * R * T x)
    (hs : ∀ᶠ x in 𝓝 x₀, p x / ρ x ^ γ = p0 / ρ0 ^ γ)
    (hen : ∀ᶠ x in 𝓝 x₀, cp * T x + u x ^ 2 / 2 = cp * T0) (hu : 0 < u x₀)
    (ha2 : a ^ 2 = γ * R * T x₀) (hM : M = |u x₀| / a) (hρ' : HasDerivAt ρ ρ' x₀)
    (hu' : HasDerivAt u u' x₀) :
    ρ' / ρ x₀ = -(M ^ 2) * (u' / u x₀) := by
  have hγ1pos : 0 < γ - 1 := by linarith
  have hγpos : 0 < γ := by linarith
  have hcp_pos : 0 < cp := by rw [hcp]; exact div_pos (mul_pos hγpos hR) hγ1pos
  have hTx := hT.self_of_nhds
  have hρx := hρ.self_of_nhds
  have henx := hen.self_of_nhds
  have hT0pos : 0 < T0 := by
    have h1 : 0 < cp * T0 := by rw [← henx]; positivity
    exact pos_of_mul_pos_right h1 hcp_pos.le
  have hlog : ∀ᶠ x in 𝓝 x₀, Real.log (ρ x) =
      Real.log ρ0 - 1 / (γ - 1) * (Real.log T0 - Real.log (T x)) := by
    filter_upwards [hT, hρ, hp, hs, hen] with x hTx' hρx' hpx hsx henx'
    have hdr := (stagnation_density_ratio (a := Real.sqrt (γ * R * T x))
      (M := |u x| / Real.sqrt (γ * R * T x)) hγ hR hTx' hcp (Real.sq_sqrt (by positivity)) rfl
      henx' hρx' hρ0 hpx hp0 hsx).1
    have h1 := congrArg Real.log hdr
    rw [Real.log_div hρ0.ne' hρx'.ne', Real.log_rpow (div_pos hT0pos hTx'),
      Real.log_div hT0pos.ne' hTx'.ne'] at h1
    linarith
  have hTeq : ∀ᶠ x in 𝓝 x₀, T x = T0 - u x ^ 2 / (2 * cp) := by
    filter_upwards [hen] with x hx
    field_simp
    linarith
  have hTd : HasDerivAt T (-(u x₀ * u') / cp) x₀ := by
    have h := ((hu'.pow 2).div_const (2 * cp)).const_sub T0
    have h' := h.congr_of_eventuallyEq hTeq
    convert h' using 1
    field_simp
    ring
  have hrhs : HasDerivAt (fun x => Real.log ρ0 - 1 / (γ - 1) * (Real.log T0 - Real.log (T x)))
      (1 / (γ - 1) * (-(u x₀ * u') / cp / T x₀)) x₀ := by
    have h := (((hTd.log hTx.ne').const_sub (Real.log T0)).const_mul (1 / (γ - 1))).const_sub
      (Real.log ρ0)
    convert h using 1
    ring
  have hlhs : HasDerivAt (fun x => Real.log (ρ x)) (ρ' / ρ x₀) x₀ := hρ'.log hρx.ne'
  have heq := hlhs.unique (hrhs.congr_of_eventuallyEq hlog)
  have hM2 : M ^ 2 = u x₀ ^ 2 / a ^ 2 := by rw [hM, div_pow, sq_abs]
  rw [heq, hM2, ha2, hcp]
  field_simp

/-- **Differentiated mass conservation.** If `ρ u A = ṁ` near the station `x₀`, the three
factors are positive at the station and have the derivatives `ρ'`, `u'`, `A'` there, then
`ρ' / ρ + u' / u + A' / A = 0`. -/
lemma mass_flow_derivative {mdot x₀ A' ρ' u' : ℝ} {A ρ u : ℝ → ℝ}
    (hmass : ∀ᶠ x in 𝓝 x₀, ρ x * u x * A x = mdot) (hρ : 0 < ρ x₀) (hu : 0 < u x₀)
    (hA : 0 < A x₀) (hA' : HasDerivAt A A' x₀) (hρ' : HasDerivAt ρ ρ' x₀)
    (hu' : HasDerivAt u u' x₀) :
    ρ' / ρ x₀ + u' / u x₀ + A' / A x₀ = 0 := by
  have hprod := (hρ'.mul hu').mul hA'
  have hconst : HasDerivAt (fun x => ρ x * u x * A x) 0 x₀ :=
    (hasDerivAt_const x₀ mdot).congr_of_eventuallyEq hmass
  have h0 := hprod.unique hconst
  simp only [Pi.mul_apply] at h0
  field_simp
  linear_combination h0

/-! ## I. The area-velocity relation and stationary area at a sonic station -/

/-- **Area-velocity relation.** Under the hypotheses of `isentropic_density_derivative`, with
`ρ u A = ṁ` near the station, `A > 0` at the station and `A` differentiable there with derivative
`A'`, the steady isentropic quasi-one-dimensional flow has `A' / A = (M ^ 2 - 1) u' / u`. -/
lemma area_velocity_relation {γ R cp T0 ρ0 p0 mdot a M x₀ A' ρ' u' : ℝ}
    {A ρ u T p : ℝ → ℝ} (hγ : 1 < γ) (hR : 0 < R) (hcp : cp = γ * R / (γ - 1))
    (hρ0 : 0 < ρ0) (hp0 : p0 = ρ0 * R * T0) (hT : ∀ᶠ x in 𝓝 x₀, 0 < T x)
    (hρ : ∀ᶠ x in 𝓝 x₀, 0 < ρ x) (hp : ∀ᶠ x in 𝓝 x₀, p x = ρ x * R * T x)
    (hs : ∀ᶠ x in 𝓝 x₀, p x / ρ x ^ γ = p0 / ρ0 ^ γ)
    (hen : ∀ᶠ x in 𝓝 x₀, cp * T x + u x ^ 2 / 2 = cp * T0)
    (hmass : ∀ᶠ x in 𝓝 x₀, ρ x * u x * A x = mdot) (hu : 0 < u x₀) (hA : 0 < A x₀)
    (ha2 : a ^ 2 = γ * R * T x₀) (hM : M = |u x₀| / a) (hA' : HasDerivAt A A' x₀)
    (hρ' : HasDerivAt ρ ρ' x₀) (hu' : HasDerivAt u u' x₀) :
    A' / A x₀ = (M ^ 2 - 1) * (u' / u x₀) := by
  have h1 := isentropic_density_derivative hγ hR hcp hρ0 hp0 hT hρ hp hs hen hu ha2 hM hρ' hu'
  have h2 := mass_flow_derivative hmass hρ.self_of_nhds hu hA hA' hρ' hu'
  linear_combination h2 - h1

/-- **A sonic station has stationary area.** Under the hypotheses of `area_velocity_relation`,
`M = 1` gives `A' = 0`: a necessary condition for a throat, not an area minimum. -/
lemma area_deriv_eq_zero_of_mach_eq_one {γ R cp T0 ρ0 p0 mdot a M x₀ A' ρ' u' : ℝ}
    {A ρ u T p : ℝ → ℝ} (hγ : 1 < γ) (hR : 0 < R) (hcp : cp = γ * R / (γ - 1))
    (hρ0 : 0 < ρ0) (hp0 : p0 = ρ0 * R * T0) (hT : ∀ᶠ x in 𝓝 x₀, 0 < T x)
    (hρ : ∀ᶠ x in 𝓝 x₀, 0 < ρ x) (hp : ∀ᶠ x in 𝓝 x₀, p x = ρ x * R * T x)
    (hs : ∀ᶠ x in 𝓝 x₀, p x / ρ x ^ γ = p0 / ρ0 ^ γ)
    (hen : ∀ᶠ x in 𝓝 x₀, cp * T x + u x ^ 2 / 2 = cp * T0)
    (hmass : ∀ᶠ x in 𝓝 x₀, ρ x * u x * A x = mdot) (hu : 0 < u x₀) (hA : 0 < A x₀)
    (ha2 : a ^ 2 = γ * R * T x₀) (hM : M = |u x₀| / a) (hA' : HasDerivAt A A' x₀)
    (hρ' : HasDerivAt ρ ρ' x₀) (hu' : HasDerivAt u u' x₀) (hM1 : M = 1) :
    A' = 0 := by
  have h := area_velocity_relation hγ hR hcp hρ0 hp0 hT hρ hp hs hen hmass hu hA ha2 hM hA' hρ'
    hu'
  rw [hM1] at h
  have h0 : A' / A x₀ = 0 := by rw [h]; ring
  exact (div_eq_zero_iff.mp h0).resolve_right hA.ne'

/-- **Stationary area with accelerating flow is sonic.** Under the hypotheses of
`area_velocity_relation` with stationary area `A' = 0`, a positive sound speed and `u' ≠ 0` at the
station, `M = 1`. -/
lemma mach_eq_one_of_area_deriv_eq_zero {γ R cp T0 ρ0 p0 mdot a M x₀ ρ' u' : ℝ}
    {A ρ u T p : ℝ → ℝ} (hγ : 1 < γ) (hR : 0 < R) (hcp : cp = γ * R / (γ - 1))
    (hρ0 : 0 < ρ0) (hp0 : p0 = ρ0 * R * T0) (hT : ∀ᶠ x in 𝓝 x₀, 0 < T x)
    (hρ : ∀ᶠ x in 𝓝 x₀, 0 < ρ x) (hp : ∀ᶠ x in 𝓝 x₀, p x = ρ x * R * T x)
    (hs : ∀ᶠ x in 𝓝 x₀, p x / ρ x ^ γ = p0 / ρ0 ^ γ)
    (hen : ∀ᶠ x in 𝓝 x₀, cp * T x + u x ^ 2 / 2 = cp * T0)
    (hmass : ∀ᶠ x in 𝓝 x₀, ρ x * u x * A x = mdot) (hu : 0 < u x₀) (hA : 0 < A x₀)
    (ha : 0 < a) (ha2 : a ^ 2 = γ * R * T x₀) (hM : M = |u x₀| / a) (hA' : HasDerivAt A 0 x₀)
    (hρ' : HasDerivAt ρ ρ' x₀) (hu' : HasDerivAt u u' x₀) (hu'0 : u' ≠ 0) :
    M = 1 := by
  have h := area_velocity_relation hγ hR hcp hρ0 hp0 hT hρ hp hs hen hmass hu hA ha2 hM hA' hρ'
    hu'
  rw [zero_div] at h
  have hq : u' / u x₀ ≠ 0 := div_ne_zero hu'0 hu.ne'
  have hM2 : M ^ 2 = 1 := by
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · linarith
    · exact absurd h1 hq
  have hMnn : 0 ≤ M := by rw [hM]; exact div_nonneg (abs_nonneg _) ha.le
  nlinarith

/-- **The choked mass flow makes the station sonic.** Under the hypotheses of
`massFlux_eq_isentropicMassFlux` at a station of area `A > 0`, if its mass flow `ρ u A = ṁ` is
selected at the choked value `ṁ = G(1) A`, the sonic maximum of the isentropic mass flux, then
`M = 1`. -/
lemma mach_eq_one_of_choked {γ R T T0 cp a u M ρ ρ0 p p0 A mdot : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hT : 0 < T) (hcp : cp = γ * R / (γ - 1)) (ha : 0 < a) (ha2 : a ^ 2 = γ * R * T)
    (hM : M = |u| / a) (hen : cp * T + u ^ 2 / 2 = cp * T0) (hρ : 0 < ρ) (hρ0 : 0 < ρ0)
    (hp : p = ρ * R * T) (hp0 : p0 = ρ0 * R * T0) (hs : p / ρ ^ γ = p0 / ρ0 ^ γ) (hA : 0 < A)
    (hmass : ρ * u * A = mdot) (hchoke : mdot = isentropicMassFlux p0 T0 R γ 1 * A) :
    M = 1 := by
  have hflux := massFlux_eq_isentropicMassFlux hγ hR hT hcp ha ha2 hM hen hρ hρ0 hp hp0 hs
  have hγpos : 0 < γ := by linarith
  have hγ1pos : 0 < γ - 1 := by linarith
  have hcp_pos : 0 < cp := by rw [hcp]; exact div_pos (mul_pos hγpos hR) hγ1pos
  have hT0pos : 0 < T0 := by
    have h1 : 0 < cp * T0 := by rw [← hen]; positivity
    exact pos_of_mul_pos_right h1 hcp_pos.le
  have hp0pos : 0 < p0 := by rw [hp0]; positivity
  have hρu : ρ * u = isentropicMassFlux p0 T0 R γ 1 :=
    mul_right_cancel₀ hA.ne' (hmass.trans hchoke)
  by_contra hM1
  have hlt := isentropicMassFlux_lt_sonic hp0pos hT0pos hR hγ hM1
  have hle : ρ * u ≤ ρ * |u| := mul_le_mul_of_nonneg_left (le_abs_self u) hρ.le
  linarith

/-! ## J. Normal-shock jump conditions and branch ratios -/

/-- The steady normal-shock jump conditions between an upstream state `(ρ1, u1, p1, T1)` and a
downstream state `(ρ2, u2, p2, T2)` of a calorically perfect gas with gas constant `R` and
heat-capacity ratio `γ`: the ideal-gas law `p = ρ R T` at both states, and conservation of the
mass flux `ρ u`, the momentum flux `p + ρ u ^ 2` and the total enthalpy `cp T + u ^ 2 / 2` with
`cp = γ R / (γ - 1)`. -/
def IsNormalShockJump (γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2 : ℝ) : Prop :=
  p1 = ρ1 * R * T1 ∧ p2 = ρ2 * R * T2 ∧ ρ1 * u1 = ρ2 * u2 ∧
    p1 + ρ1 * u1 ^ 2 = p2 + ρ2 * u2 ^ 2 ∧
    γ * R / (γ - 1) * T1 + u1 ^ 2 / 2 = γ * R / (γ - 1) * T2 + u2 ^ 2 / 2

/-- The density ratio `ρ2 / ρ1 = (γ + 1) m / ((γ - 1) m + 2)` of the distinct normal-shock
branch, at the squared upstream Mach number `m = M1 ^ 2`. -/
noncomputable def shockDensityRatio (γ m : ℝ) : ℝ :=
  (γ + 1) * m / ((γ - 1) * m + 2)

/-- The pressure ratio `p2 / p1 = (2 γ m - (γ - 1)) / (γ + 1)` of the distinct normal-shock
branch, at `m = M1 ^ 2`. -/
noncomputable def shockPressureRatio (γ m : ℝ) : ℝ :=
  (2 * γ * m - (γ - 1)) / (γ + 1)

/-- The temperature ratio `T2 / T1` of the distinct normal-shock branch: the pressure ratio over
the density ratio. -/
noncomputable def shockTemperatureRatio (γ m : ℝ) : ℝ :=
  shockPressureRatio γ m / shockDensityRatio γ m

/-! ## K. The two normal-shock branches -/

/-- The trivial branch always exists: a perfect-gas state `p1 = ρ1 R T1` satisfies the jump
conditions with itself as the downstream state. -/
lemma isNormalShockJump_self {γ R ρ1 u1 p1 T1 : ℝ} (hp1 : p1 = ρ1 * R * T1) :
    IsNormalShockJump γ R ρ1 u1 p1 T1 ρ1 u1 p1 T1 := by
  unfold IsNormalShockJump
  exact ⟨hp1, hp1, rfl, rfl, rfl⟩

/-- The distinct branch solves the jump conditions: for `γ > 1`, `R > 0`, an upstream perfect-gas
state `p1 = ρ1 R T1` with `T1 > 0` and `u1 > 0`, sound speed `a1 ^ 2 = γ R T1` and Mach number
`M1 = |u1| / a1`, the state with `ρ2 = ρ1 r`, `u2 = u1 / r`, `p2 = p1 P` and `T2 = T1 P / r`,
where `r` and `P` are the density and pressure ratios at `m = M1 ^ 2`, satisfies the jump
conditions. This holds whatever the sign of `P`: it is an algebraic statement, and
`isNormalShockJump_distinct_pos_iff` says when the root is a positive state. -/
lemma isNormalShockJump_distinct {γ R ρ1 u1 p1 T1 a1 M1 : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hT1 : 0 < T1) (hu1 : 0 < u1) (hp1 : p1 = ρ1 * R * T1) (ha1 : a1 ^ 2 = γ * R * T1)
    (hM1 : M1 = |u1| / a1) :
    IsNormalShockJump γ R ρ1 u1 p1 T1 (ρ1 * shockDensityRatio γ (M1 ^ 2))
      (u1 / shockDensityRatio γ (M1 ^ 2)) (p1 * shockPressureRatio γ (M1 ^ 2))
      (T1 * shockTemperatureRatio γ (M1 ^ 2)) := by
  have hγpos : 0 < γ := by linarith
  have hγ1pos : 0 < γ + 1 := by linarith
  have hγ1ne : γ + 1 ≠ 0 := ne_of_gt hγ1pos
  have ha1sqpos : 0 < a1 ^ 2 := by
    rw [ha1]
    exact mul_pos (mul_pos hγpos hR) hT1
  have ha1ne : a1 ≠ 0 := by
    intro h
    have hz : a1 ^ 2 = 0 := by simp [h]
    rw [hz] at ha1sqpos
    exact lt_irrefl 0 ha1sqpos
  have hu1ne : u1 ≠ 0 := ne_of_gt hu1
  have habspos : 0 < |u1| := abs_pos.mpr hu1ne
  have habsne : |u1| ≠ 0 := ne_of_gt habspos
  have hM1ne : M1 ≠ 0 := by
    rw [hM1]
    exact div_ne_zero habsne ha1ne
  have hmpos : 0 < M1 ^ 2 := sq_pos_of_ne_zero hM1ne
  have hmne : M1 ^ 2 ≠ 0 := ne_of_gt hmpos
  have hDpos : 0 < (γ - 1) * M1 ^ 2 + 2 := by
    have h1 : 0 ≤ (γ - 1) * M1 ^ 2 := by
      apply mul_nonneg
      · linarith
      · exact sq_nonneg M1
    linarith
  have hDne : (γ - 1) * M1 ^ 2 + 2 ≠ 0 := ne_of_gt hDpos
  have hrpos : 0 < shockDensityRatio γ (M1 ^ 2) := by
    unfold shockDensityRatio
    exact div_pos (mul_pos hγ1pos hmpos) hDpos
  have hrne : shockDensityRatio γ (M1 ^ 2) ≠ 0 := ne_of_gt hrpos
  have hγRT1pos : 0 < γ * R * T1 := mul_pos (mul_pos hγpos hR) hT1
  have hγRT1ne : γ * R * T1 ≠ 0 := ne_of_gt hγRT1pos
  have hγsubpos : 0 < γ - 1 := by linarith
  have hγsubne : γ - 1 ≠ 0 := ne_of_gt hγsubpos
  have hNne : (γ + 1) * M1 ^ 2 ≠ 0 := mul_ne_zero hγ1ne hmne
  have hm : M1 ^ 2 = u1 ^ 2 / (γ * R * T1) := by
    rw [hM1, div_pow, sq_abs, ha1]
  have hm' : M1 ^ 2 * (γ * R * T1) = u1 ^ 2 := by
    rw [hm, div_mul_cancel₀ _ hγRT1ne]
  unfold IsNormalShockJump
  refine ⟨hp1, ?_, ?_, ?_, ?_⟩
  · unfold shockTemperatureRatio
    field_simp
    linear_combination (shockPressureRatio γ (M1 ^ 2)) * hp1
  · field_simp
  · unfold shockDensityRatio shockPressureRatio
    field_simp
    have hKey : ((p1 + ρ1 * u1 ^ 2) * (γ + 1) - p1 * (2 * γ * M1 ^ 2 - (γ - 1))) * M1 ^ 2
        - ρ1 * u1 ^ 2 * ((γ - 1) * M1 ^ 2 + 2) = 0 := by
      linear_combination (-2 * γ * M1 ^ 2 * (M1 ^ 2 - 1)) * hp1
        + (-2 * (M1 ^ 2 - 1) * ρ1) * hm'
    linear_combination hKey
  · unfold shockTemperatureRatio shockDensityRatio shockPressureRatio
    field_simp
    have hKey : (γ * R * T1 * 2 + (γ - 1) * u1 ^ 2) * (γ + 1) ^ 2 * M1 ^ 4
        - ((γ - 1) * M1 ^ 2 + 2)
          * (γ * R * T1 * 2 * M1 ^ 2 * (2 * γ * M1 ^ 2 - (γ - 1))
            + (γ - 1) * u1 ^ 2 * ((γ - 1) * M1 ^ 2 + 2)) = 0 := by
      linear_combination
        ((γ - 1) * (((γ - 1) * M1 ^ 2 + 2) ^ 2 - (γ + 1) ^ 2 * (M1 ^ 2) ^ 2)) * hm'
    linear_combination hKey

/-- **Branch classification on the positive domain.** For `γ > 1`, `R > 0`, an upstream state
with `ρ1, T1 > 0`, sound speed `a1 ^ 2 = γ R T1`, Mach number `M1 = |u1| / a1`, and a downstream
state with `ρ2, T2 > 0` satisfying the jump conditions, either the downstream state is the
upstream one (trivial branch), or `ρ2 / ρ1`, `p2 / p1` and `T2 / T1` are the density, pressure
and temperature ratios of the distinct branch at `m = M1 ^ 2`, and then
`m > (γ - 1) / (2 γ)`. With zero velocity the trivial branch is forced, so no sign hypothesis on
`u1` is needed here. -/
lemma normalShock_classification {γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2 a1 M1 : ℝ} (hγ : 1 < γ)
    (hR : 0 < R) (hρ1 : 0 < ρ1) (hT1 : 0 < T1) (hρ2 : 0 < ρ2) (hT2 : 0 < T2)
    (ha1 : a1 ^ 2 = γ * R * T1) (hM1 : M1 = |u1| / a1)
    (hjump : IsNormalShockJump γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2) :
    (ρ2 = ρ1 ∧ u2 = u1 ∧ p2 = p1 ∧ T2 = T1) ∨
      (ρ2 / ρ1 = shockDensityRatio γ (M1 ^ 2) ∧ p2 / p1 = shockPressureRatio γ (M1 ^ 2) ∧
        T2 / T1 = shockTemperatureRatio γ (M1 ^ 2) ∧ (γ - 1) / (2 * γ) < M1 ^ 2) := by
  have hγpos : 0 < γ := by linarith
  have hγne : γ ≠ 0 := ne_of_gt hγpos
  have hRne : R ≠ 0 := ne_of_gt hR
  have hT1ne : T1 ≠ 0 := ne_of_gt hT1
  have hγsubpos : 0 < γ - 1 := by linarith
  have hγsubne : γ - 1 ≠ 0 := ne_of_gt hγsubpos
  have hρ2ne : ρ2 ≠ 0 := ne_of_gt hρ2
  obtain ⟨hp1, hp2, hmass, hmom, henth⟩ := hjump
  have henth' : γ * R * T1 + (γ - 1) * (u1 ^ 2 / 2)
      = γ * R * T2 + (γ - 1) * (u2 ^ 2 / 2) := by
    have h := congrArg (fun x => x * (γ - 1)) henth
    field_simp at h
    linear_combination h / 2
  have hfact : ρ2 * (u1 - u2) * ((γ + 1) * u1 * u2 - (γ - 1) * u1 ^ 2 - 2 * γ * R * T1)
      = 0 := by
    linear_combination (-2 * γ * u1) * hp1 + (2 * γ * u1) * hp2
      + (-2 * γ * R * T1 - 2 * γ * u1 ^ 2) * hmass
      + (2 * γ * u1) * hmom + (-2 * u1 * ρ2) * henth'
  have hCase : u1 = u2 ∨ (γ + 1) * u1 * u2 - (γ - 1) * u1 ^ 2 - 2 * γ * R * T1 = 0 := by
    rcases mul_eq_zero.mp hfact with h12 | hG
    · rcases mul_eq_zero.mp h12 with hρ | hu
      · exfalso
        exact hρ2ne hρ
      · left
        exact sub_eq_zero.mp hu
    · right
      exact hG
  rcases hCase with hu12 | hG
  · have hu21 : u2 = u1 := hu12.symm
    have hCne : γ * R / (γ - 1) ≠ 0 :=
      div_ne_zero (mul_ne_zero hγne hRne) hγsubne
    by_cases hu1zero : u1 = 0
    · have hu2zero : u2 = 0 := by rw [hu21, hu1zero]
      have hmom0 : p1 = p2 := by
        rw [hu1zero, hu2zero] at hmom
        simpa using hmom
      have hp : p2 = p1 := hmom0.symm
      have hCT : γ * R / (γ - 1) * T1 = γ * R / (γ - 1) * T2 := by
        rw [hu1zero, hu2zero] at henth
        simpa using henth
      have hT12 : T1 = T2 := mul_left_cancel₀ hCne hCT
      have hT : T2 = T1 := hT12.symm
      have hp2' := hp2
      rw [hT] at hp2'
      have hRT1ne : R * T1 ≠ 0 := mul_ne_zero hRne hT1ne
      have hρmul : ρ2 * (R * T1) = ρ1 * (R * T1) := by
        linear_combination -hp2' + hp1 + hp
      have hρ : ρ2 = ρ1 := mul_right_cancel₀ hRT1ne hρmul
      left
      exact ⟨hρ, hu21, hp, hT⟩
    · have hmass' : ρ1 * u1 = ρ2 * u1 := by rw [←hu12] at hmass; exact hmass
      have hρ12 : ρ1 = ρ2 := mul_right_cancel₀ hu1zero hmass'
      have hρ : ρ2 = ρ1 := hρ12.symm
      have hmom' : p1 + ρ1 * u1 ^ 2 = p2 + ρ1 * u1 ^ 2 := by
        rw [hρ, ←hu12] at hmom
        exact hmom
      have hp : p2 = p1 := by linarith
      have henth'2 : γ * R / (γ - 1) * T1 + u1 ^ 2 / 2
          = γ * R / (γ - 1) * T2 + u1 ^ 2 / 2 := by
        rw [←hu12] at henth
        exact henth
      have hCT : γ * R / (γ - 1) * T1 = γ * R / (γ - 1) * T2 := by
        linear_combination henth'2
      have hT12 : T1 = T2 := mul_left_cancel₀ hCne hCT
      have hT : T2 = T1 := hT12.symm
      left
      exact ⟨hρ, hu21, hp, hT⟩
  · have hγ1pos : 0 < γ + 1 := by linarith
    have hγ1ne : γ + 1 ≠ 0 := ne_of_gt hγ1pos
    have hγRT1pos : 0 < γ * R * T1 := mul_pos (mul_pos hγpos hR) hT1
    have hγRT1ne : γ * R * T1 ≠ 0 := ne_of_gt hγRT1pos
    have h2γRT1pos : 0 < 2 * γ * R * T1 :=
      mul_pos (mul_pos (mul_pos (by norm_num) hγpos) hR) hT1
    have hu1ne : u1 ≠ 0 := by
      intro h
      rw [h] at hG
      linarith
    have hu2ne : u2 ≠ 0 := by
      intro h
      rw [h] at hG
      have h1 : 0 ≤ (γ - 1) * u1 ^ 2 :=
        mul_nonneg (le_of_lt hγsubpos) (sq_nonneg u1)
      linarith
    have ha1sqpos : 0 < a1 ^ 2 := by
      rw [ha1]
      exact mul_pos (mul_pos hγpos hR) hT1
    have ha1ne : a1 ≠ 0 := by
      intro h
      have hz : a1 ^ 2 = 0 := by simp [h]
      rw [hz] at ha1sqpos
      exact lt_irrefl 0 ha1sqpos
    have hm : M1 ^ 2 = u1 ^ 2 / (γ * R * T1) := by
      rw [hM1, div_pow, sq_abs, ha1]
    have hm' : M1 ^ 2 * (γ * R * T1) = u1 ^ 2 := by
      rw [hm, div_mul_cancel₀ _ hγRT1ne]
    have hDpos : 0 < (γ - 1) * M1 ^ 2 + 2 := by
      have h1 : 0 ≤ (γ - 1) * M1 ^ 2 :=
        mul_nonneg (le_of_lt hγsubpos) (sq_nonneg M1)
      linarith
    have hDne : (γ - 1) * M1 ^ 2 + 2 ≠ 0 := ne_of_gt hDpos
    have hρ1ne : ρ1 ≠ 0 := ne_of_gt hρ1
    have hp1pos : 0 < p1 := by
      rw [hp1]
      exact mul_pos (mul_pos hρ1 hR) hT1
    have hp1ne : p1 ≠ 0 := ne_of_gt hp1pos
    have hp2pos : 0 < p2 := by
      rw [hp2]
      exact mul_pos (mul_pos hρ2 hR) hT2
    have hG1mul : (ρ2 * ((γ - 1) * M1 ^ 2 + 2) - ρ1 * (γ + 1) * M1 ^ 2) * (γ * R * T1)
        = 0 := by
      linear_combination (ρ2 * (γ - 1) - ρ1 * (γ + 1)) * hm'
        + (-ρ2) * hG + (-(γ + 1) * u1) * hmass
    have hG1 : ρ2 * ((γ - 1) * M1 ^ 2 + 2) - ρ1 * (γ + 1) * M1 ^ 2 = 0 :=
      (mul_eq_zero.mp hG1mul).resolve_right hγRT1ne
    have hρ : ρ2 / ρ1 = shockDensityRatio γ (M1 ^ 2) := by
      unfold shockDensityRatio
      rw [div_eq_div_iff hρ1ne hDne]
      linear_combination hG1
    have hG2mul : (p2 * (γ + 1) - p1 * (2 * γ * M1 ^ 2 - (γ - 1))) * (γ * R * T1)
        = 0 := by
      linear_combination (-(γ * R * T1) * ρ1) * hG
        + ((γ * R * T1) * (γ + 1) * u2) * hmass
        + (2 * γ * (γ * R * T1 - u1 ^ 2)) * hp1
        + (-(γ * R * T1) * (γ + 1)) * hmom + (-2 * γ * p1) * hm'
    have hG2 : p2 * (γ + 1) - p1 * (2 * γ * M1 ^ 2 - (γ - 1)) = 0 :=
      (mul_eq_zero.mp hG2mul).resolve_right hγRT1ne
    have hp : p2 / p1 = shockPressureRatio γ (M1 ^ 2) := by
      unfold shockPressureRatio
      rw [div_eq_div_iff hp1ne hγ1ne]
      linear_combination hG2
    have hTmul : T2 * p1 * ρ2 - p2 * ρ1 * T1 = 0 := by
      linear_combination T2 * ρ2 * hp1 - ρ1 * T1 * hp2
    have hρdivne : ρ2 / ρ1 ≠ 0 := ne_of_gt (div_pos hρ2 hρ1)
    have hPr : shockTemperatureRatio γ (M1 ^ 2) = (p2 / p1) / (ρ2 / ρ1) := by
      unfold shockTemperatureRatio
      rw [←hp, ←hρ]
    have hT : T2 / T1 = shockTemperatureRatio γ (M1 ^ 2) := by
      rw [hPr]
      field_simp
      linear_combination hTmul
    have hPpos : 0 < shockPressureRatio γ (M1 ^ 2) := by
      rw [←hp]
      exact div_pos hp2pos hp1pos
    have hQ : shockPressureRatio γ (M1 ^ 2) * (γ + 1)
        = 2 * γ * M1 ^ 2 - (γ - 1) := by
      unfold shockPressureRatio
      exact div_mul_cancel₀ _ hγ1ne
    have hnum : 0 < 2 * γ * M1 ^ 2 - (γ - 1) := by
      have h2 := mul_pos hPpos hγ1pos
      rw [hQ] at h2
      exact h2
    have hthresh : (γ - 1) / (2 * γ) < M1 ^ 2 := by
      have h2γpos : 0 < 2 * γ := by linarith
      rw [div_lt_iff₀ h2γpos]
      linear_combination hnum
    right
    exact ⟨hρ, hp, hT, hthresh⟩

/-- **The distinct branch is physical only above the pressure-positivity threshold.** Under the
hypotheses of `isNormalShockJump_distinct` with `ρ1 > 0`, the distinct root has positive density,
and it has positive pressure and temperature exactly when `M1 ^ 2 > (γ - 1) / (2 γ)`. -/
lemma isNormalShockJump_distinct_pos_iff {γ R ρ1 u1 p1 T1 a1 M1 : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hρ1 : 0 < ρ1) (hT1 : 0 < T1) (hu1 : 0 < u1) (hp1 : p1 = ρ1 * R * T1)
    (ha1 : a1 ^ 2 = γ * R * T1) (hM1 : M1 = |u1| / a1) :
    0 < ρ1 * shockDensityRatio γ (M1 ^ 2) ∧
      (0 < p1 * shockPressureRatio γ (M1 ^ 2) ∧ 0 < T1 * shockTemperatureRatio γ (M1 ^ 2) ↔
        (γ - 1) / (2 * γ) < M1 ^ 2) := by
  have hγpos : 0 < γ := by linarith
  have hγ1pos : 0 < γ + 1 := by linarith
  have hγ1ne : γ + 1 ≠ 0 := ne_of_gt hγ1pos
  have hγne : γ ≠ 0 := ne_of_gt hγpos
  have ha1sqpos : 0 < a1 ^ 2 := by
    rw [ha1]
    exact mul_pos (mul_pos hγpos hR) hT1
  have ha1ne : a1 ≠ 0 := by
    intro h
    have hz : a1 ^ 2 = 0 := by simp [h]
    rw [hz] at ha1sqpos
    exact lt_irrefl 0 ha1sqpos
  have hu1ne : u1 ≠ 0 := ne_of_gt hu1
  have habspos : 0 < |u1| := abs_pos.mpr hu1ne
  have habsne : |u1| ≠ 0 := ne_of_gt habspos
  have hM1ne : M1 ≠ 0 := by
    rw [hM1]
    exact div_ne_zero habsne ha1ne
  have hmpos : 0 < M1 ^ 2 := sq_pos_of_ne_zero hM1ne
  have hDpos : 0 < (γ - 1) * M1 ^ 2 + 2 := by
    have h1 : 0 ≤ (γ - 1) * M1 ^ 2 := by
      apply mul_nonneg
      · linarith
      · exact sq_nonneg M1
    linarith
  have hrpos : 0 < shockDensityRatio γ (M1 ^ 2) := by
    unfold shockDensityRatio
    exact div_pos (mul_pos hγ1pos hmpos) hDpos
  have hρrpos : 0 < ρ1 * shockDensityRatio γ (M1 ^ 2) := mul_pos hρ1 hrpos
  have hp1pos : 0 < p1 := by
    rw [hp1]
    exact mul_pos (mul_pos hρ1 hR) hT1
  have hPpos_iff_Qpos :
      0 < shockPressureRatio γ (M1 ^ 2) ↔ 0 < 2 * γ * M1 ^ 2 - (γ - 1) := by
    unfold shockPressureRatio
    constructor
    · intro h
      have h2 := mul_pos h hγ1pos
      rw [div_mul_cancel₀ _ hγ1ne] at h2
      exact h2
    · intro h
      have hγ1invpos : 0 < (γ + 1)⁻¹ := inv_pos.mpr hγ1pos
      have h3 := mul_pos h hγ1invpos
      rwa [div_eq_mul_inv]
  have hQpos_iff_thresh :
      0 < 2 * γ * M1 ^ 2 - (γ - 1) ↔ (γ - 1) / (2 * γ) < M1 ^ 2 := by
    have h2γpos : 0 < 2 * γ := by linarith
    rw [div_lt_iff₀ h2γpos]
    have heq : 2 * γ * M1 ^ 2 - (γ - 1) = M1 ^ 2 * (2 * γ) - (γ - 1) := by ring
    rw [heq]
    constructor <;> intro h <;> linarith
  have hPiff : 0 < shockPressureRatio γ (M1 ^ 2) ↔ (γ - 1) / (2 * γ) < M1 ^ 2 :=
    hPpos_iff_Qpos.trans hQpos_iff_thresh
  refine ⟨hρrpos, ?_⟩
  constructor
  · intro h
    obtain ⟨h1, _⟩ := h
    have hPpos : 0 < shockPressureRatio γ (M1 ^ 2) :=
      pos_of_mul_pos_right h1 (le_of_lt hp1pos)
    exact hPiff.mp hPpos
  · intro hthresh
    have hPpos : 0 < shockPressureRatio γ (M1 ^ 2) := hPiff.mpr hthresh
    have h1 : 0 < p1 * shockPressureRatio γ (M1 ^ 2) := mul_pos hp1pos hPpos
    have hTPr : T1 * shockTemperatureRatio γ (M1 ^ 2)
        = T1 * shockPressureRatio γ (M1 ^ 2) / shockDensityRatio γ (M1 ^ 2) := by
      unfold shockTemperatureRatio
      rw [mul_div_assoc]
    have h2 : 0 < T1 * shockTemperatureRatio γ (M1 ^ 2) := by
      rw [hTPr]
      exact div_pos (mul_pos hT1 hPpos) hrpos
    exact ⟨h1, h2⟩

/-- **The roots coincide at `m = 1`.** For `γ > 1` and `m ≥ 0`, the density ratio and the
pressure ratio of the distinct branch equal `1` exactly when `m = 1`, and at `m = 1` the
temperature ratio is `1`: the distinct branch is then the trivial one. -/
lemma shockRatio_eq_one_iff {γ m : ℝ} (hγ : 1 < γ) (hm : 0 ≤ m) :
    (shockDensityRatio γ m = 1 ↔ m = 1) ∧ (shockPressureRatio γ m = 1 ↔ m = 1) ∧
      (m = 1 → shockTemperatureRatio γ m = 1) := by
  have hγpos : 0 < γ := by linarith
  have hγ1pos : 0 < γ + 1 := by linarith
  have hγ1ne : γ + 1 ≠ 0 := ne_of_gt hγ1pos
  have hDpos : 0 < (γ - 1) * m + 2 := by
    have h1 : 0 ≤ (γ - 1) * m := by
      apply mul_nonneg
      · linarith
      · exact hm
    linarith
  have hDne : (γ - 1) * m + 2 ≠ 0 := ne_of_gt hDpos
  have hDens : shockDensityRatio γ m = 1 ↔ m = 1 := by
    constructor
    · intro hr
      unfold shockDensityRatio at hr
      have hr2 : (γ + 1) * m = (γ - 1) * m + 2 := by
        have h := congrArg (fun x => x * ((γ - 1) * m + 2)) hr
        rw [div_mul_cancel₀ _ hDne, one_mul] at h
        exact h
      have h2 : 2 * m = 2 := by linear_combination hr2
      linarith
    · intro hm1
      unfold shockDensityRatio
      rw [hm1]
      have hN : (γ + 1) * (1 : ℝ) = (γ - 1) * 1 + 2 := by ring
      have hD1ne : (γ - 1) * (1 : ℝ) + 2 ≠ 0 := by
        have : (γ - 1) * (1 : ℝ) + 2 = γ + 1 := by ring
        rw [this]
        exact hγ1ne
      rw [hN, div_self hD1ne]
  have hPress : shockPressureRatio γ m = 1 ↔ m = 1 := by
    constructor
    · intro hp
      unfold shockPressureRatio at hp
      have hp2 : 2 * γ * m - (γ - 1) = γ + 1 := by
        have h := congrArg (fun x => x * (γ + 1)) hp
        rw [div_mul_cancel₀ _ hγ1ne, one_mul] at h
        exact h
      have h2 : γ * m = γ * 1 := by linear_combination hp2 / 2
      have hγne : γ ≠ 0 := ne_of_gt hγpos
      exact mul_left_cancel₀ hγne h2
    · intro hm1
      unfold shockPressureRatio
      rw [hm1]
      have hN : 2 * γ * (1 : ℝ) - (γ - 1) = γ + 1 := by ring
      rw [hN, div_self hγ1ne]
  refine ⟨hDens, hPress, ?_⟩
  intro hm1
  have hr : shockDensityRatio γ m = 1 := hDens.mpr hm1
  have hp : shockPressureRatio γ m = 1 := hPress.mpr hm1
  unfold shockTemperatureRatio
  rw [hr, hp, div_self (one_ne_zero)]

/-! ## L. Specific entropy change in `(T, p)` form and on the distinct branch -/

/-- The entropy change per unit mass of a calorically perfect gas from the state `(T1, v1)` to the
state `(T2, v2)`: `cv log (T2 / T1) + R log (v2 / v1)`, with the specific heat at constant volume
`cv`, the specific gas constant `R` and the specific volumes `v1`, `v2` (`v = 1 / ρ`). Domain:
positive temperatures and specific volumes; elsewhere `Real.log` returns a junk value. -/
noncomputable def specificEntropyChange (cv R T1 v1 T2 v2 : ℝ) : ℝ :=
  cv * Real.log (T2 / T1) + R * Real.log (v2 / v1)

/-- **The `(T, p)` form of the specific entropy change.** For `γ > 1`, `R > 0`, the specific heat
`cv = R / (γ - 1)` and two states with positive densities and temperatures obeying `p = ρ R T`,
the specific entropy change between the specific volumes `1 / ρ1` and `1 / ρ2` is
`cp log (T2 / T1) - R log (p2 / p1)` with `cp = γ R / (γ - 1)`. -/
lemma specificEntropyChange_perfectGas {γ R ρ1 p1 T1 ρ2 p2 T2 : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hρ1 : 0 < ρ1) (hT1 : 0 < T1) (hρ2 : 0 < ρ2) (hT2 : 0 < T2) (hp1 : p1 = ρ1 * R * T1)
    (hp2 : p2 = ρ2 * R * T2) :
    specificEntropyChange (R / (γ - 1)) R T1 (1 / ρ1) T2 (1 / ρ2) =
      γ * R / (γ - 1) * Real.log (T2 / T1) - R * Real.log (p2 / p1) := by
  have hγ1 : γ - 1 ≠ 0 := (sub_pos.mpr hγ).ne'
  have hpp : p2 / p1 = ρ2 / ρ1 * (T2 / T1) := by
    rw [hp1, hp2]
    field_simp
  have hV : 1 / ρ2 / (1 / ρ1) = (ρ2 / ρ1)⁻¹ := by
    field_simp
  unfold specificEntropyChange
  rw [hpp, hV, Real.log_inv, Real.log_mul (div_pos hρ2 hρ1).ne' (div_pos hT2 hT1).ne']
  field_simp
  ring

/-- The dimensionless entropy jump `Δs / R = log P / (γ - 1) - γ log r / (γ - 1)` of the distinct
normal-shock branch at `m = M1 ^ 2`, with its pressure ratio `P` and density ratio `r`. Domain:
`γ > 1` and `m > (γ - 1) / (2 γ)`, where `P, r > 0`; below the threshold `P ≤ 0` and
`Real.log` returns a junk value. -/
noncomputable def shockEntropyJump (γ m : ℝ) : ℝ :=
  Real.log (shockPressureRatio γ m) / (γ - 1) - γ * Real.log (shockDensityRatio γ m) / (γ - 1)

/-- **No jump at `m = 1`.** For `γ > 1` both ratios are `1` at `m = 1`, so `Δs / R = 0`. -/
lemma shockEntropyJump_one {γ : ℝ} (hγ : 1 < γ) : shockEntropyJump γ 1 = 0 := by
  have h := shockRatio_eq_one_iff hγ zero_le_one
  unfold shockEntropyJump
  rw [h.1.mpr rfl, h.2.1.mpr rfl, Real.log_one]
  ring

private lemma shockRatios_pos {γ m : ℝ} (hγ : 1 < γ) (hm : (γ - 1) / (2 * γ) < m) :
    0 < m ∧ 0 < (γ - 1) * m + 2 ∧ 0 < 2 * γ * m - γ + 1 ∧
      0 < shockPressureRatio γ m ∧ 0 < shockDensityRatio γ m := by
  have hγ0 : 0 < γ := by linarith
  have hθ : 0 < (γ - 1) / (2 * γ) := div_pos (by linarith) (by linarith)
  have hm0 : 0 < m := lt_trans hθ hm
  have hD : 0 < (γ - 1) * m + 2 := by nlinarith
  have hQ : 0 < 2 * γ * m - γ + 1 := by
    rw [div_lt_iff₀ (by linarith)] at hm
    linarith
  refine ⟨hm0, hD, hQ, ?_, ?_⟩
  · unfold shockPressureRatio
    exact div_pos (by linarith) (by linarith)
  · unfold shockDensityRatio
    exact div_pos (mul_pos (by linarith) hm0) hD

/-- **Derivative of the entropy jump.** For `γ > 1` and `m > (γ - 1) / (2 γ)`, `Δs / R` has the
derivative `2 γ (m - 1) ^ 2 / (m ((γ - 1) m + 2) (2 γ m - γ + 1))` in `m`. -/
lemma hasDerivAt_shockEntropyJump {γ m : ℝ} (hγ : 1 < γ) (hm : (γ - 1) / (2 * γ) < m) :
    HasDerivAt (shockEntropyJump γ)
      (2 * γ * (m - 1) ^ 2 / (m * ((γ - 1) * m + 2) * (2 * γ * m - γ + 1))) m := by
  obtain ⟨hm0, hD, hQ, hP, hr⟩ := shockRatios_pos hγ hm
  have hγ1 : γ - 1 ≠ 0 := (sub_pos.mpr hγ).ne'
  have hγp1 : γ + 1 ≠ 0 := by linarith
  have hPd : HasDerivAt (fun x => shockPressureRatio γ x) (2 * γ / (γ + 1)) m := by
    have h := (((hasDerivAt_id' m).const_mul (2 * γ)).sub_const (γ - 1)).div_const (γ + 1)
    simpa [shockPressureRatio] using h
  have hrd : HasDerivAt (fun x => shockDensityRatio γ x)
      (2 * (γ + 1) / ((γ - 1) * m + 2) ^ 2) m := by
    have hnum := (hasDerivAt_id' m).const_mul (γ + 1)
    have hden := ((hasDerivAt_id' m).const_mul (γ - 1)).add_const 2
    have h := hnum.div hden hD.ne'
    unfold shockDensityRatio
    convert h using 1
    field_simp
    ring
  have hlogP := hPd.log hP.ne'
  have hlogr := hrd.log hr.ne'
  have h := (hlogP.div_const (γ - 1)).sub ((hlogr.const_mul γ).div_const (γ - 1))
  have hQ1 : 2 * γ * m - (γ - 1) ≠ 0 := by
    have : 2 * γ * m - (γ - 1) = 2 * γ * m - γ + 1 := by ring
    rw [this]
    exact hQ.ne'
  have hm1 : m ≠ 0 := hm0.ne'
  have hD1 : (γ - 1) * m + 2 ≠ 0 := hD.ne'
  unfold shockEntropyJump
  convert h using 1
  unfold shockPressureRatio shockDensityRatio
  rw [show 2 * γ * m - γ + 1 = 2 * γ * m - (γ - 1) by ring]
  rw [div_eq_iff (mul_ne_zero (mul_ne_zero hm1 hD1) hQ1)]
  field_simp
  ring

private lemma shockEntropyJump_strictMonoOn {γ : ℝ} (hγ : 1 < γ) :
    StrictMonoOn (shockEntropyJump γ) (Set.Ioi ((γ - 1) / (2 * γ))) := by
  have hθ1 : (γ - 1) / (2 * γ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hpos : ∀ m, (γ - 1) / (2 * γ) < m → m ≠ 1 →
      0 < 2 * γ * (m - 1) ^ 2 / (m * ((γ - 1) * m + 2) * (2 * γ * m - γ + 1)) := by
    intro m hm hm1
    obtain ⟨hm0, hD, hQ, -, -⟩ := shockRatios_pos hγ hm
    have hsq : 0 < (m - 1) ^ 2 := by
      have : m - 1 ≠ 0 := sub_ne_zero.mpr hm1
      positivity
    exact div_pos (mul_pos (by linarith) hsq) (mul_pos (mul_pos hm0 hD) hQ)
  have h1 : StrictMonoOn (shockEntropyJump γ) (Set.Ioc ((γ - 1) / (2 * γ)) 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) ?_ ?_
    · exact fun m hm => (hasDerivAt_shockEntropyJump hγ hm.1).continuousAt.continuousWithinAt
    · intro m hm
      rw [interior_Ioc] at hm
      rw [(hasDerivAt_shockEntropyJump hγ hm.1).deriv]
      exact hpos m hm.1 (ne_of_lt hm.2)
  have h2 : StrictMonoOn (shockEntropyJump γ) (Set.Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · exact fun m hm =>
        (hasDerivAt_shockEntropyJump hγ (lt_of_lt_of_le hθ1 hm)).continuousAt.continuousWithinAt
    · intro m hm
      rw [interior_Ici] at hm
      rw [(hasDerivAt_shockEntropyJump hγ (lt_trans hθ1 hm)).deriv]
      exact hpos m (lt_trans hθ1 hm) (ne_of_gt hm)
  intro a ha b hb hab
  rcases le_or_gt b 1 with hb1 | hb1
  · exact h1 ⟨ha, le_trans hab.le hb1⟩ ⟨hb, hb1⟩ hab
  · rcases le_or_gt 1 a with ha1 | ha1
    · exact h2 ha1 hb1.le hab
    · calc shockEntropyJump γ a < shockEntropyJump γ 1 := h1 ⟨ha, ha1.le⟩ ⟨hθ1, le_rfl⟩ ha1
        _ < shockEntropyJump γ b := h2 le_rfl hb1.le hb1

/-- **Sign of the entropy jump.** For `γ > 1` and `m > (γ - 1) / (2 γ)`, `Δs / R > 0` exactly for
`m > 1` and `Δs / R < 0` exactly for `m < 1`. -/
lemma shockEntropyJump_pos_iff {γ m : ℝ} (hγ : 1 < γ) (hm : (γ - 1) / (2 * γ) < m) :
    (0 < shockEntropyJump γ m ↔ 1 < m) ∧ (shockEntropyJump γ m < 0 ↔ m < 1) := by
  have hmono := shockEntropyJump_strictMonoOn hγ
  have h1 := shockEntropyJump_one hγ
  have hθ1 : (γ - 1) / (2 * γ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hgt : 1 < m → 0 < shockEntropyJump γ m := fun h => by
    have := hmono (show (1 : ℝ) ∈ Set.Ioi ((γ - 1) / (2 * γ)) from hθ1) hm h
    rwa [h1] at this
  have hlt : m < 1 → shockEntropyJump γ m < 0 := fun h => by
    have := hmono hm (show (1 : ℝ) ∈ Set.Ioi ((γ - 1) / (2 * γ)) from hθ1) h
    rwa [h1] at this
  refine ⟨⟨fun hpos => ?_, hgt⟩, ⟨fun hneg => ?_, hlt⟩⟩
  · rcases lt_trichotomy m 1 with h | h | h
    · exact absurd (hlt h) (not_lt.mpr hpos.le)
    · rw [h, h1] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h
  · rcases lt_trichotomy m 1 with h | h | h
    · exact h
    · rw [h, h1] at hneg
      exact absurd hneg (lt_irrefl 0)
    · exact absurd (hgt h) (not_lt.mpr hneg.le)

/-- **Entropy change across the nontrivial branch.** Under the hypotheses of
`normalShock_classification`, a solution other than the trivial branch is the distinct branch
above the threshold with `M1 ^ 2 ≠ 1`, and its specific entropy change is `R` times
`shockEntropyJump γ (M1 ^ 2)`. -/
lemma normalShock_entropyChange {γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2 a1 M1 : ℝ} (hγ : 1 < γ)
    (hR : 0 < R) (hρ1 : 0 < ρ1) (hT1 : 0 < T1) (hρ2 : 0 < ρ2) (hT2 : 0 < T2)
    (ha1 : a1 ^ 2 = γ * R * T1) (hM1 : M1 = |u1| / a1)
    (hjump : IsNormalShockJump γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2)
    (hnt : ¬(ρ2 = ρ1 ∧ u2 = u1 ∧ p2 = p1 ∧ T2 = T1)) :
    (γ - 1) / (2 * γ) < M1 ^ 2 ∧ M1 ^ 2 ≠ 1 ∧
      specificEntropyChange (R / (γ - 1)) R T1 (1 / ρ1) T2 (1 / ρ2) =
        R * shockEntropyJump γ (M1 ^ 2) := by
  have hγ1 : γ - 1 ≠ 0 := (sub_pos.mpr hγ).ne'
  obtain ⟨hp1, hp2, hmass, -, -⟩ := id hjump
  have hp1pos : 0 < p1 := by rw [hp1]; positivity
  have hp2pos : 0 < p2 := by rw [hp2]; positivity
  rcases normalShock_classification hγ hR hρ1 hT1 hρ2 hT2 ha1 hM1 hjump with htriv |
    ⟨hr, hP, hT, hthr⟩
  · exact absurd htriv hnt
  have hm1 : M1 ^ 2 ≠ 1 := by
    intro hm
    have h := shockRatio_eq_one_iff hγ (sq_nonneg M1)
    have hρ : ρ2 = ρ1 := by
      rw [h.1.mpr hm, div_eq_one_iff_eq hρ1.ne'] at hr
      exact hr
    have hp : p2 = p1 := by
      rw [h.2.1.mpr hm, div_eq_one_iff_eq hp1pos.ne'] at hP
      exact hP
    have hTT : T2 = T1 := by
      rw [h.2.2 hm, div_eq_one_iff_eq hT1.ne'] at hT
      exact hT
    have hu : u2 = u1 := by
      rw [hρ] at hmass
      exact (mul_left_cancel₀ hρ1.ne' hmass).symm
    exact hnt ⟨hρ, hu, hp, hTT⟩
  refine ⟨hthr, hm1, ?_⟩
  obtain ⟨-, -, -, hPpos, hrpos⟩ := shockRatios_pos hγ hthr
  rw [specificEntropyChange_perfectGas hγ hR hρ1 hT1 hρ2 hT2 hp1 hp2, hT, hP]
  unfold shockTemperatureRatio shockEntropyJump
  rw [Real.log_div hPpos.ne' hrpos.ne']
  field_simp
  ring

/-! ## M. Selection of the compression branch -/

/-- **Entropy selects the compression branch.** Under the hypotheses of
`normalShock_entropyChange` and the flow orientation `M1 > 0`, the entropy rises across the jump
exactly for `M1 > 1` and falls exactly for `M1 < 1`. -/
lemma normalShock_entropy_pos_iff {γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2 a1 M1 : ℝ} (hγ : 1 < γ)
    (hR : 0 < R) (hρ1 : 0 < ρ1) (hT1 : 0 < T1) (hρ2 : 0 < ρ2) (hT2 : 0 < T2)
    (ha1 : a1 ^ 2 = γ * R * T1) (hM1 : M1 = |u1| / a1) (hM1pos : 0 < M1)
    (hjump : IsNormalShockJump γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2)
    (hnt : ¬(ρ2 = ρ1 ∧ u2 = u1 ∧ p2 = p1 ∧ T2 = T1)) :
    (0 < specificEntropyChange (R / (γ - 1)) R T1 (1 / ρ1) T2 (1 / ρ2) ↔ 1 < M1) ∧
      (specificEntropyChange (R / (γ - 1)) R T1 (1 / ρ1) T2 (1 / ρ2) < 0 ↔ M1 < 1) := by
  obtain ⟨hthr, -, hS⟩ := normalShock_entropyChange hγ hR hρ1 hT1 hρ2 hT2 ha1 hM1 hjump hnt
  obtain ⟨hpos, hneg⟩ := shockEntropyJump_pos_iff hγ hthr
  have hsq1 : 1 < M1 ^ 2 ↔ 1 < M1 := ⟨fun h => by nlinarith, fun h => by nlinarith⟩
  have hsq2 : M1 ^ 2 < 1 ↔ M1 < 1 := ⟨fun h => by nlinarith, fun h => by nlinarith⟩
  rw [hS]
  constructor
  · rw [← hsq1, ← hpos]
    exact ⟨fun h => pos_of_mul_pos_right h hR.le, fun h => mul_pos hR h⟩
  · rw [← hsq2, ← hneg]
    exact ⟨fun h => neg_of_mul_neg_right h hR.le, fun h => mul_neg_of_pos_of_neg hR h⟩

/-- **Unchanged total enthalpy and `p02 / p01 = exp (-Δs / R)`.** For a positive-state solution
of the jump conditions, with each stagnation state fixed by the stagnation energy balance
`cp T + u ^ 2 / 2 = cp T0`, the ideal-gas law and the declared isentropic connection
`p / ρ ^ γ = p0 / ρ0 ^ γ` with a positive stagnation density, the stagnation temperatures agree
and the stagnation pressure ratio is `exp (-Δs / R)`, on either branch. -/
lemma normalShock_stagnationPressure_ratio
    {γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2 ρ01 p01 T01 ρ02 p02 T02 : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hρ1 : 0 < ρ1) (hT1 : 0 < T1) (hρ2 : 0 < ρ2) (hT2 : 0 < T2)
    (hjump : IsNormalShockJump γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2)
    (hen1 : γ * R / (γ - 1) * T1 + u1 ^ 2 / 2 = γ * R / (γ - 1) * T01)
    (hen2 : γ * R / (γ - 1) * T2 + u2 ^ 2 / 2 = γ * R / (γ - 1) * T02)
    (hρ01 : 0 < ρ01) (hρ02 : 0 < ρ02) (hp01 : p01 = ρ01 * R * T01) (hp02 : p02 = ρ02 * R * T02)
    (hs1 : p1 / ρ1 ^ γ = p01 / ρ01 ^ γ) (hs2 : p2 / ρ2 ^ γ = p02 / ρ02 ^ γ) :
    T02 = T01 ∧ p02 / p01 =
      Real.exp (-(specificEntropyChange (R / (γ - 1)) R T1 (1 / ρ1) T2 (1 / ρ2) / R)) := by
  have hγ1 : 0 < γ - 1 := sub_pos.mpr hγ
  have hγ0 : 0 < γ := by linarith
  have hcp : 0 < γ * R / (γ - 1) := div_pos (mul_pos hγ0 hR) hγ1
  obtain ⟨hp1, hp2, -, -, henth⟩ := id hjump
  have hT0 : T02 = T01 := by
    have h : γ * R / (γ - 1) * T02 = γ * R / (γ - 1) * T01 := by linarith
    exact mul_left_cancel₀ hcp.ne' h
  refine ⟨hT0, ?_⟩
  have hstag : ∀ {ρ u p T ρ0 p0 T0 : ℝ}, 0 < ρ → 0 < T → p = ρ * R * T → 0 < ρ0 →
      p0 = ρ0 * R * T0 → γ * R / (γ - 1) * T + u ^ 2 / 2 = γ * R / (γ - 1) * T0 →
      p / ρ ^ γ = p0 / ρ0 ^ γ → p0 / p = (T0 / T) ^ (γ / (γ - 1)) := by
    intro ρ u p T ρ0 p0 T0 hρ hT hp hρ0 hp0 hen hs
    have ha : Real.sqrt (γ * R * T) ^ 2 = γ * R * T := Real.sq_sqrt (by positivity)
    exact (stagnation_pressure_ratio hγ hR hT rfl ha rfl hen hρ hρ0 hp hp0 hs).1
  have h1 := hstag hρ1 hT1 hp1 hρ01 hp01 hen1 hs1
  have h2 := hstag hρ2 hT2 hp2 hρ02 hp02 hen2 hs2
  have hT01 : 0 < T01 := by
    have h : 0 < γ * R / (γ - 1) * T01 := by rw [← hen1]; positivity
    exact pos_of_mul_pos_right h hcp.le
  have hp1pos : 0 < p1 := by rw [hp1]; positivity
  have hp2pos : 0 < p2 := by rw [hp2]; positivity
  rw [specificEntropyChange_perfectGas hγ hR hρ1 hT1 hρ2 hT2 hp1 hp2]
  have hexp : -((γ * R / (γ - 1) * Real.log (T2 / T1) - R * Real.log (p2 / p1)) / R) =
      Real.log (p2 / p1) + Real.log (T1 / T2) * (γ / (γ - 1)) := by
    rw [show T1 / T2 = (T2 / T1)⁻¹ by rw [inv_div], Real.log_inv]
    field_simp
    ring
  rw [hexp, Real.exp_add, Real.exp_log (div_pos hp2pos hp1pos),
    ← Real.rpow_def_of_pos (div_pos hT1 hT2)]
  have e1 : p01 = p1 * (T01 / T1) ^ (γ / (γ - 1)) := by
    rw [← h1]
    field_simp
  have e2 : p02 = p2 * (T01 / T2) ^ (γ / (γ - 1)) := by
    rw [← hT0, ← h2]
    field_simp
  have hsplit : (T01 / T2) ^ (γ / (γ - 1)) =
      (T1 / T2) ^ (γ / (γ - 1)) * (T01 / T1) ^ (γ / (γ - 1)) := by
    rw [← Real.mul_rpow (div_pos hT1 hT2).le (div_pos hT01 hT1).le]
    congr 1
    field_simp
  have hpow : 0 < (T01 / T1) ^ (γ / (γ - 1)) := Real.rpow_pos_of_pos (div_pos hT01 hT1) _
  rw [e1, e2, hsplit]
  field_simp

/-- **Total pressure across the two branches.** Under the hypotheses of
`normalShock_entropy_pos_iff` and the stagnation hypotheses of
`normalShock_stagnationPressure_ratio`: for `M1 > 1` the total pressure falls, `p02 < p01`; for
`M1 < 1` the solution is on the positive-state expansion branch
`(γ - 1) / (2 γ) < M1 ^ 2 < 1`, where the total pressure rises, `p01 < p02`, and the entropy
falls: the expansion root is entropy-inadmissible. -/
lemma normalShock_totalPressure_selection
    {γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2 a1 M1 ρ01 p01 T01 ρ02 p02 T02 : ℝ} (hγ : 1 < γ) (hR : 0 < R)
    (hρ1 : 0 < ρ1) (hT1 : 0 < T1) (hρ2 : 0 < ρ2) (hT2 : 0 < T2)
    (ha1 : a1 ^ 2 = γ * R * T1) (hM1 : M1 = |u1| / a1) (hM1pos : 0 < M1)
    (hjump : IsNormalShockJump γ R ρ1 u1 p1 T1 ρ2 u2 p2 T2)
    (hnt : ¬(ρ2 = ρ1 ∧ u2 = u1 ∧ p2 = p1 ∧ T2 = T1))
    (hen1 : γ * R / (γ - 1) * T1 + u1 ^ 2 / 2 = γ * R / (γ - 1) * T01)
    (hen2 : γ * R / (γ - 1) * T2 + u2 ^ 2 / 2 = γ * R / (γ - 1) * T02)
    (hρ01 : 0 < ρ01) (hρ02 : 0 < ρ02) (hp01 : p01 = ρ01 * R * T01) (hp02 : p02 = ρ02 * R * T02)
    (hs1 : p1 / ρ1 ^ γ = p01 / ρ01 ^ γ) (hs2 : p2 / ρ2 ^ γ = p02 / ρ02 ^ γ) :
    (1 < M1 → p02 < p01) ∧
      (M1 < 1 → (γ - 1) / (2 * γ) < M1 ^ 2 ∧ M1 ^ 2 < 1 ∧ p01 < p02 ∧
        specificEntropyChange (R / (γ - 1)) R T1 (1 / ρ1) T2 (1 / ρ2) < 0) := by
  have hγ1 : 0 < γ - 1 := sub_pos.mpr hγ
  have hcp : 0 < γ * R / (γ - 1) := div_pos (mul_pos (by linarith) hR) hγ1
  obtain ⟨hthr, -, -⟩ := normalShock_entropyChange hγ hR hρ1 hT1 hρ2 hT2 ha1 hM1 hjump hnt
  obtain ⟨hpos, hneg⟩ :=
    normalShock_entropy_pos_iff hγ hR hρ1 hT1 hρ2 hT2 ha1 hM1 hM1pos hjump hnt
  obtain ⟨-, hratio⟩ := normalShock_stagnationPressure_ratio hγ hR hρ1 hT1 hρ2 hT2 hjump hen1
    hen2 hρ01 hρ02 hp01 hp02 hs1 hs2
  have hT01 : 0 < T01 := by
    have h : 0 < γ * R / (γ - 1) * T01 := by rw [← hen1]; positivity
    exact pos_of_mul_pos_right h hcp.le
  have hp01pos : 0 < p01 := by rw [hp01]; positivity
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hΔ := hpos.mpr h
    have hlt : p02 / p01 < 1 := by
      rw [hratio, Real.exp_lt_one_iff, neg_lt_zero]
      exact div_pos hΔ hR
    exact (div_lt_one hp01pos).mp hlt
  · have hΔ := hneg.mpr h
    have hgt : 1 < p02 / p01 := by
      rw [hratio, Real.one_lt_exp_iff, neg_pos]
      exact div_neg_of_neg_of_pos hΔ hR
    exact ⟨hthr, by nlinarith, (one_lt_div hp01pos).mp hgt, hΔ⟩

end FluidDynamics.PerfectGasPorts
