/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.Extr
public import PhyslibExt.EarthScience.IsothermalAtmosphericPressure

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.ODE.InvariantRegions

/-!
# Aircraft performance: isothermal density, drag polar, power required and jet range

## i. Overview

In an isothermal hydrostatic layer with constant gravity, the density at height `z` above the
reference level is the mass-specific ideal-gas relation `ρ = p / (Rs * T)` applied to the
existing isothermal pressure profile `EarthScience.isothermalPressure`, with reference pressure
`ρ0 * Rs * T`. It equals `ρ0 * exp (-z / H)` with scale height `H = Rs * T / |g|`.

Model inputs: hydrostatic balance and the ideal-gas equation of state (both carried by the
pressure profile), constant absolute temperature `T > 0`, constant gravity of magnitude `g > 0`
with `z` measured upward, mass-specific gas constant `Rs > 0` and reference density `ρ0 > 0`.
The model is asserted only on a declared finite band `[z₁, z₂]` of heights: the band results
carry `z ∈ Set.Icc z₁ z₂`, and `isothermalDensity_band_bounds_fail_outside` shows that the
band bounds are false outside the band. Variable-temperature standard atmospheres and rarefied
flow are different models and are not claimed. Each result assumes only the hypotheses its
proof uses.

Units: a change of units multiplies a coordinate of dimension `M^a L^b T^c Θ^d` by
`m^a * l^b * s^c * k^d`, where `m, l, s, k > 0` count the new mass, length, time and
temperature units in one old unit (metres to kilometres: `l = 1 / 1000`). The density formula
commutes with every such change. A Celsius reading is affine, not a coordinate of a change of
units, and is never a valid `T`.

An airplane of weight `W` with wing area `S` flies straight and level at speed `V > 0` through
air of density `ρ`. Its drag follows the declared parabolic polar `CD = CD0 + k * CL ^ 2` at
dynamic pressure `ρ * V ^ 2 / 2`, so `D = ρ * V ^ 2 / 2 * S * (CD0 + k * CL ^ 2)`. Level flight
with thrust along the velocity imposes the vertical balance `L = W`, which fixes
`CL = 2 * W / (ρ * V ^ 2 * S)`. Substituting gives `D(V) = a * V ^ 2 + b / V ^ 2` with
`a = ρ * S * CD0 / 2` (parasite drag) and `b = 2 * k * W ^ 2 / (ρ * S)` (induced drag). By the
arithmetic-geometric mean inequality `D(V) ≥ 2 * √(a * b)`, with equality exactly when
`V ^ 4 = b / a`; for `CD0, k > 0` and positive weight this is the minimum-drag speed
`V_md = (b / a) ^ (1 / 4)`. The density input may be the isothermal-layer density above
(`two_sqrt_le_levelDrag_isothermalDensity`).

Level-flight model inputs: steady level flight with thrust aligned with the velocity (an
inclined thrust line would add a vertical thrust component to the lift balance, which is not
modelled), the declared polar with positive coefficients `CD0, k`, and positive `ρ, S` and
weight `W`. The results that describe the airplane (its least drag and minimum-drag speed, its
stall-validity interval) take `W > 0`, and so does the lift-to-drag remark at
`two_sqrt_mul_dragFactor_eq`: in level flight the lift equals the weight. The least-drag results
`levelDrag_eq_two_sqrt_iff_eq_minDragSpeed` and `isLeast_levelDrag` take `W > 0` although their
proofs need only `W ≠ 0`; apart from them, each result assumes only the hypotheses its proof
uses. Lemmas about the drag formulas alone (`inducedDragFactor_pos`, `minDragSpeed_pos`,
`minDragSpeed_pow_four`, `two_sqrt_mul_dragFactor_eq`) hold for any nonzero `W`, or any `W`,
because the drag depends on `W` only through `W ^ 2`. Outside the regime, with `ρ, S > 0` and
`CD0, k ≥ 0`, the parasite term `a * V ^ 2` vanishes exactly when `CD0 = 0` and the induced term
`b / V ^ 2` exactly when `k = 0` or `W = 0`. If exactly one of them vanishes, `D(V)` is the other
term alone, strictly monotone over positive speeds, and has no minimum there; if both vanish,
`D(V) = 0` at every speed, so every positive speed minimizes it. In each of these cases
`minDragSpeed` takes the value `0`, which is not a positive speed. The polar is valid only up to a
declared maximum lift coefficient `CLmax`; at a positive speed this is the stall-validity interval
`V ≥ V_s = √(2 * W / (ρ * S * CLmax))`, whose radicand is positive only for `W > 0`.
The algebraic minimizer is an operating point only when it lies in that interval:
`exists_levelDrag_eq_two_sqrt_iff` and `two_sqrt_lt_levelDrag_of_minDragSpeed_lt_stallSpeed`. At
`V = 0` Lean's convention `x / 0 = 0` gives meaningless values; no statement uses them.

The power required at speed `V > 0` on the same polar is the thrust power
`P(V) = D(V) * V = a * V ^ 3 + b / V`: the thrust `T = D` works at the rate `T * V`. Its
derivative `3 * a * V ^ 2 - b / V ^ 2` vanishes at a positive speed exactly when
`V ^ 4 = b / (3 * a)`, and for `CD0 > 0` a positive speed minimizes `P` over positive speeds
exactly then (`isMinOn_levelPower_iff`, which needs no sign of `k` or `W`). For positive weight
and `k > 0` this is the unique minimum-power speed `V_mp = (b / (3 * a)) ^ (1 / 4)`; `P` strictly
decreases on `(0, V_mp]` and strictly increases on `[V_mp, ∞)`. This optimum is not the
minimum-drag speed: `V_md ^ 4 = 3 * V_mp ^ 4`, so `V_mp = V_md / 3 ^ (1 / 4)`, about
`0.76 * V_md`; the power at `V_md` exceeds `P(V_mp)`; and the lift coefficient at `V_mp` is
`√(3 * CD0 / k)`, `√3` times the one at `V_md`, where the induced drag is three times the
parasite drag. On the stall-validity interval the least power is attained exactly at
`max V_s V_mp`: at `V_mp` when it is admissible, otherwise at the stall endpoint `V_s`; and
`V_mp < V_s` exactly when `CLmax < √(3 * CD0 / k)`.

Power model inputs: the level-flight inputs above at a fixed altitude (fixed `ρ`). `P` is the
power delivered by the thrust, not the shaft power: a propulsor of efficiency `η` must absorb
`P / η`, which equals `P` only at `η = 1`; for a constant `η > 0` the minimizing speed is
unchanged. A speed-dependent efficiency is not modelled. As for drag, the results that describe
the airplane take `W > 0` although their proofs need only `W ≠ 0`, and the formula lemmas for
`minPowerSpeed` take `W ≠ 0`; at `V = 0` both `levelPower` and its cubic form take the
meaningless value `0`.

A jet in quasi-level cruise burns fuel at a weight rate proportional to its thrust,
`W' = -cW * T`, with the weight `W` a force and the weight-based coefficient `cW` an inverse time
(weight flow per unit thrust). Thrust along the velocity balances the drag and the lift balances
the weight, so at a fixed lift coefficient `CL` on the polar `T = D = W / Λ` with
`Λ = CL / (CD0 + k * CL ^ 2)`, and `W' = -cW * W / Λ`. From `W(0) = Wi` the solution is
`W(t) = Wi * exp (-(cW / Λ) * t)` (`cruiseWeight_solves`, through
`MetaMathlibExt.scalar_exp_solution`), and it is the only one: along any solution
`W(t) * exp ((cW / Λ) * t)` has derivative zero. The weight falls from `Wi` to `Wf` in the time
`Λ / cW * log (Wi / Wf)`, positive for `Wi > Wf > 0` and zero for `Wi = Wf`; at the constant air
speed `V` the air-path distance flown is `V` times that time, the thrust-specific (jet) Breguet
range `V * Λ / cW * log (Wi / Wf)`. A mass-based coefficient `cm` (fuel mass flow per unit
thrust) gives `cW = g * cm` for the weight `W = g * m`; using `cm` in place of `cW` multiplies the
duration and the range by `g`.

Cruise schedule: constant `V` and fixed `CL` (hence fixed `Λ`) with falling weight need the
density `ρ(t) = 2 * W(t) / (V ^ 2 * S * CL)`. At a fixed altitude the lift stays fixed and cannot
balance the falling weight. In an isothermal layer of scale height `H` the required density is
met by the steady climb `z(t) = z₀ + H * (cW / Λ) * t`, and only by it; the cruise climbs
`H * log (Wi / Wf)` in all, and the model applies only while the climb stays in the layer's
declared band (`cruiseClimb_mem_band_iff`).

Cruise model inputs: idealized quasi-steady cruise with constant `V`, `Λ` and `cW`, lift equal to
weight and thrust equal to drag at every instant, so the climb work and the flight-path angle of
the cruise-climb are neglected: a quasi-level model, not an exact climbing-trajectory solution.
The fuel law is the thrust-specific jet law, not a propeller law. The final weight `Wf` is a
declared input; reserve and dry-weight bounds are separate. Distance is air-path length at the
declared speed, not ground range. Each cruise result assumes only the hypotheses its proof uses.

## ii. Key results

- `AircraftPerformance.isothermalDensity_eq_exp`: `ρ(z) = ρ0 * exp (-z / H)`.
- `AircraftPerformance.hasDerivAt_isothermalPressure_density`: `p'(z) = -ρ(z) * g`.
- `AircraftPerformance.isothermalDensity_band_bounds`: positive monotone bounds on a band.
- `AircraftPerformance.isothermalDensity_band_bounds_fail_outside`: no extrapolation.
- `AircraftPerformance.isothermalDensity_unitChange`, `scaleHeight_unitChange`: units.
- `AircraftPerformance.polarDrag_eq_levelDrag`: level flight turns the polar into
  `D(V) = a * V ^ 2 + b / V ^ 2`.
- `AircraftPerformance.two_sqrt_le_levelDrag`: `2 * √(a * b) ≤ D(V)`.
- `AircraftPerformance.levelDrag_eq_two_sqrt_iff`: equality exactly when `V ^ 4 = b / a`.
- `AircraftPerformance.isLeast_levelDrag`: the least drag over positive speeds.
- `AircraftPerformance.exists_levelDrag_eq_two_sqrt_iff`: the bound is attained by an admissible
  speed exactly when `V_s ≤ V_md`.
- `AircraftPerformance.levelPower_eq`, `polarDrag_mul_eq_levelPower`: the power required
  `P(V) = a * V ^ 3 + b / V`, the polar drag times the speed in level flight.
- `AircraftPerformance.isMinOn_levelPower_iff`: least power among positive speeds exactly when
  `V ^ 4 = b / (3 * a)`.
- `AircraftPerformance.levelPower_minPowerSpeed_lt`, `isLeast_levelPower`: `V_mp` is the unique
  positive minimizer.
- `AircraftPerformance.minPowerSpeed_lt_minDragSpeed`: `V_mp < V_md`.
- `AircraftPerformance.isLeast_levelPower_stall`: the least admissible power is at
  `max V_s V_mp`.
- `AircraftPerformance.shaftPowerRequired_eq_levelPower_iff`: the efficiency is not silently one.
- `AircraftPerformance.polarDrag_eq_div_polarLiftToDrag`: `D = W / Λ` at a fixed `CL`.
- `AircraftPerformance.cruiseWeight_solves`, `eq_cruiseWeight_of_hasDerivAt`: the weight history
  exists and is unique.
- `AircraftPerformance.cruise_duration_eq`, `cruise_range_eq`: the time from `Wi` to `Wf` is
  `Λ / cW * log (Wi / Wf)`, and the distance flown is `V` times that time.
- `AircraftPerformance.cruise_duration_mass_eq`, `breguetDuration_mass_confusion`: the mass-based
  coefficient.
- `AircraftPerformance.lift_ne_cruiseWeight_of_fixed_density`: no fixed-altitude cruise.
- `AircraftPerformance.lift_cruiseClimb`, `cruiseClimb_mem_band_iff`: the isothermal cruise-climb
  and its altitude-band check.

## iii. Table of contents

- A. Scale height and density
- B. Bounds on a declared band
- C. Change of units
- D. Level flight on the declared polar
- E. Minimum drag
- F. The stall-validity interval
- G. Isothermal-layer density as the density input
- H. Power required
- I. Minimum power
- J. Distinct from the minimum-drag speed
- K. Power on the stall-validity interval
- L. Shaft power
- M. Thrust-specific fuel law in quasi-level cruise
- N. The weight history
- O. Duration and range
- P. Mass-based fuel coefficient
- Q. The cruise schedule

## iv. References

- J. D. Anderson, *Introduction to Flight*, McGraw-Hill, ch. 3 (the standard atmosphere and
  its isothermal layers, `ρ / ρ₁ = exp (-(g₀ / (R T)) (h - h₁))`) and ch. 6 (drag polar
  `CD = CD0 + K * CL ^ 2`, thrust required in level flight, minimum thrust required where
  zero-lift drag equals drag due to lift, and for positive weight
  `(L / D)max = 1 / (2 * √(K * CD0))`; power required `P_R = T_R * V`, minimum power required
  where the zero-lift drag is one third of the drag due to lift, at `CL = √(3 * CD0 / K)` and
  below the speed of minimum thrust required; power available as shaft power times propeller
  efficiency; thrust-specific fuel consumption and jet endurance
  `(1 / c_t) * (CL / CD) * ln (W0 / W1)` at constant `CL / CD`).
- D. P. Raymer, *Aircraft Design: A Conceptual Approach*, AIAA, ch. 17 (level-flight
  performance and stall speed `V_s = √(2 * W / (ρ * S * CLmax))`; Breguet range and endurance
  with a weight-based thrust-specific fuel consumption; cruise-climb).
- ISO 2533:1975, *Standard Atmosphere*: the layer from 11 km to 20 km is isothermal at
  216.65 K, with `g₀ = 9.80665 m/s²`.
-/

@[expose] public section

namespace AircraftPerformance

open EarthScience

/-! ## A. Scale height and density -/

/-- Scale height `H = Rs * T / |g|` of an isothermal layer with mass-specific gas constant `Rs`,
absolute temperature `T` and gravitational acceleration of magnitude `|g|`; it is a length.
At `g = 0` Lean's convention `x / 0 = 0` gives the meaningless value `0`. -/
noncomputable def scaleHeight (Rs T g : ℝ) : ℝ := Rs * T / |g|

/-- Density at height `z` of the isothermal layer with reference density `ρ0`: the ideal-gas
relation `ρ = p / (Rs * T)` applied to `isothermalPressure` with reference pressure `ρ0 * Rs * T`,
that is `ρ0 * exp (-g * z / (Rs * T))` for `Rs * T ≠ 0`; with the convention `x / 0 = 0` it is `0`
when `Rs * T = 0`. The physical regime is `ρ0, g, Rs, T > 0`, `z` upward, `z` in a declared band. -/
noncomputable def isothermalDensity (ρ0 g Rs T z : ℝ) : ℝ :=
  isothermalPressure (ρ0 * Rs * T) g Rs T z / (Rs * T)

/-- For `g, Rs, T > 0`, the density obtained from the pressure profile and the ideal-gas relation is
`ρ(z) = ρ0 * exp (-z / H)` with `H = Rs * T / |g|`. -/
lemma isothermalDensity_eq_exp {g Rs T : ℝ} (hg : 0 < g) (hRs : 0 < Rs) (hT : 0 < T)
    (ρ0 z : ℝ) :
    isothermalDensity ρ0 g Rs T z = ρ0 * Real.exp (-z / scaleHeight Rs T g) := by
  have hg' : g ≠ 0 := ne_of_gt hg
  have hRT : (Rs * T : ℝ) ≠ 0 := mul_ne_zero (ne_of_gt hRs) (ne_of_gt hT)
  have habs : |g| = g := abs_of_pos hg
  have harg : (-g * z / (Rs * T) : ℝ) = -z / scaleHeight Rs T g := by
    unfold scaleHeight
    rw [habs]
    field_simp
  unfold isothermalDensity isothermalPressure
  rw [harg]
  field_simp

/-- Hydrostatic balance in density form: for all real inputs, the pressure profile with reference
pressure `ρ0 * Rs * T` satisfies `p'(z) = -ρ(z) * g` for `ρ = isothermalDensity ρ0 g Rs T` (both
sides are `0` when `Rs * T = 0`, by the convention `x / 0 = 0`). -/
lemma hasDerivAt_isothermalPressure_density (ρ0 g Rs T z : ℝ) :
    HasDerivAt (isothermalPressure (ρ0 * Rs * T) g Rs T)
      (-(isothermalDensity ρ0 g Rs T z) * g) z := by
  unfold isothermalDensity
  exact hasDerivAt_isothermalPressure _ _ _ _ _

/-- The density is positive at every height when `ρ0, Rs, T > 0`. -/
lemma isothermalDensity_pos {ρ0 Rs T : ℝ} (hρ0 : 0 < ρ0) (hRs : 0 < Rs) (hT : 0 < T)
    (g z : ℝ) : 0 < isothermalDensity ρ0 g Rs T z := by
  unfold isothermalDensity
  exact div_pos (isothermalPressure_pos (mul_pos (mul_pos hρ0 hRs) hT) g Rs T z)
    (mul_pos hRs hT)

/-- The scale height is positive for `Rs, T > 0` and nonzero gravity. -/
lemma scaleHeight_pos {Rs T g : ℝ} (hRs : 0 < Rs) (hT : 0 < T) (hg : g ≠ 0) :
    0 < scaleHeight Rs T g := by
  unfold scaleHeight
  exact div_pos (mul_pos hRs hT) (abs_pos.mpr hg)

/-! ## B. Bounds on a declared band -/

/-- For `ρ0, g, Rs, T > 0`, on a declared band `[z₁, z₂]` the density strictly decreases with
height. -/
lemma isothermalDensity_strictAntiOn {ρ0 g Rs T : ℝ} (hρ0 : 0 < ρ0) (hg : 0 < g)
    (hRs : 0 < Rs) (hT : 0 < T) (z₁ z₂ : ℝ) :
    StrictAntiOn (isothermalDensity ρ0 g Rs T) (Set.Icc z₁ z₂) := by
  have hRT : (0:ℝ) < Rs * T := mul_pos hRs hT
  have hpress := isothermalPressure_strictAnti (mul_pos (mul_pos hρ0 hRs) hT) hg hRs hT
  intro a _ b _ hab
  unfold isothermalDensity
  exact (div_lt_div_iff_of_pos_right hRT).mpr (hpress hab)

/-- Engineering density bounds on a declared band: for `ρ0, g, Rs, T > 0` and `z ∈ [z₁, z₂]`,
`0 < ρ0 * exp (-z₂ / H) ≤ ρ(z) ≤ ρ0 * exp (-z₁ / H)`. -/
lemma isothermalDensity_band_bounds {ρ0 g Rs T z₁ z₂ z : ℝ} (hρ0 : 0 < ρ0) (hg : 0 < g)
    (hRs : 0 < Rs) (hT : 0 < T) (hz : z ∈ Set.Icc z₁ z₂) :
    0 < ρ0 * Real.exp (-z₂ / scaleHeight Rs T g) ∧
      ρ0 * Real.exp (-z₂ / scaleHeight Rs T g) ≤ isothermalDensity ρ0 g Rs T z ∧
      isothermalDensity ρ0 g Rs T z ≤ ρ0 * Real.exp (-z₁ / scaleHeight Rs T g) := by
  have hH : (0:ℝ) < scaleHeight Rs T g := scaleHeight_pos hRs hT (ne_of_gt hg)
  have hρ0' : (0:ℝ) ≤ ρ0 := le_of_lt hρ0
  obtain ⟨h1, h2⟩ := hz
  rw [isothermalDensity_eq_exp hg hRs hT]
  refine ⟨mul_pos hρ0 (Real.exp_pos _), ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hH).mpr (neg_le_neg h2))) hρ0'
  · exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hH).mpr (neg_le_neg h1))) hρ0'

/-- For `ρ0, g, Rs, T > 0` the band bounds do not extend beyond the band: below `z₁` the density
exceeds the upper bound `ρ0 * exp (-z₁ / H)`, and above `z₂` it falls below the lower bound
`ρ0 * exp (-z₂ / H)`. The band hypothesis of `isothermalDensity_band_bounds` cannot be dropped. -/
lemma isothermalDensity_band_bounds_fail_outside {ρ0 g Rs T z₁ z₂ z : ℝ} (hρ0 : 0 < ρ0)
    (hg : 0 < g) (hRs : 0 < Rs) (hT : 0 < T) :
    (z < z₁ → ρ0 * Real.exp (-z₁ / scaleHeight Rs T g) < isothermalDensity ρ0 g Rs T z) ∧
      (z₂ < z → isothermalDensity ρ0 g Rs T z < ρ0 * Real.exp (-z₂ / scaleHeight Rs T g)) := by
  have hH : (0:ℝ) < scaleHeight Rs T g := scaleHeight_pos hRs hT (ne_of_gt hg)
  rw [isothermalDensity_eq_exp hg hRs hT]
  constructor
  · intro h
    exact mul_lt_mul_of_pos_left
      (Real.exp_strictMono ((div_lt_div_iff_of_pos_right hH).mpr (neg_lt_neg h))) hρ0
  · intro h
    exact mul_lt_mul_of_pos_left
      (Real.exp_strictMono ((div_lt_div_iff_of_pos_right hH).mpr (neg_lt_neg h))) hρ0

/-! ## C. Change of units

Density has dimension `M L⁻³`, gravity `L T⁻²`, the mass-specific gas constant
`L² T⁻² Θ⁻¹`, temperature `Θ` and height `L`. -/

/-- For `Rs, T > 0`, the density formula commutes with a change of units with length, time and
temperature factors `l, s, k > 0`, for every real `m` (the mass factor of a change of units when
`m > 0`): rescaled inputs give the rescaled density. -/
lemma isothermalDensity_unitChange (m : ℝ) {l s k Rs T : ℝ} (hl : 0 < l) (hs : 0 < s)
    (hk : 0 < k) (hRs : 0 < Rs) (hT : 0 < T) (ρ0 g z : ℝ) :
    isothermalDensity (m / l ^ 3 * ρ0) (l / s ^ 2 * g) (l ^ 2 / (s ^ 2 * k) * Rs) (k * T)
        (l * z) = m / l ^ 3 * isothermalDensity ρ0 g Rs T z := by
  have hl' : l ≠ 0 := ne_of_gt hl
  have hs' : s ≠ 0 := ne_of_gt hs
  have hk' : k ≠ 0 := ne_of_gt hk
  have hRs' : Rs ≠ 0 := ne_of_gt hRs
  have hT' : T ≠ 0 := ne_of_gt hT
  have hs2 : (s ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hs'
  have hsk : (s ^ 2 * k : ℝ) ≠ 0 := mul_ne_zero hs2 hk'
  have hl3 : (l ^ 3 : ℝ) ≠ 0 := pow_ne_zero 3 hl'
  have hRT : (Rs * T : ℝ) ≠ 0 := mul_ne_zero hRs' hT'
  have hRs'' : (l ^ 2 / (s ^ 2 * k) * Rs : ℝ) ≠ 0 :=
    mul_ne_zero (div_ne_zero (pow_ne_zero 2 hl') hsk) hRs'
  have hkT : (k * T : ℝ) ≠ 0 := mul_ne_zero hk' hT'
  have hD' : ((l ^ 2 / (s ^ 2 * k) * Rs) * (k * T) : ℝ) ≠ 0 := mul_ne_zero hRs'' hkT
  have hE : (-(l / s ^ 2 * g) * (l * z) / ((l ^ 2 / (s ^ 2 * k) * Rs) * (k * T)) : ℝ)
      = -g * z / (Rs * T) := by
    field_simp
  unfold isothermalDensity isothermalPressure
  rw [hE]
  field_simp

/-- The scale height transforms as a length under a change of units with length, time and
temperature factors `l, s, k > 0`. -/
lemma scaleHeight_unitChange {l s k : ℝ} (hl : 0 < l) (hs : 0 < s) (hk : 0 < k)
    (Rs T g : ℝ) :
    scaleHeight (l ^ 2 / (s ^ 2 * k) * Rs) (k * T) (l / s ^ 2 * g) = l * scaleHeight Rs T g := by
  have hl' : l ≠ 0 := ne_of_gt hl
  have hs' : s ≠ 0 := ne_of_gt hs
  have hk' : k ≠ 0 := ne_of_gt hk
  have hs2 : (s ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hs'
  have hsk : (s ^ 2 * k : ℝ) ≠ 0 := mul_ne_zero hs2 hk'
  have hls : (0:ℝ) < l / s ^ 2 := div_pos hl (pow_pos hs 2)
  unfold scaleHeight
  by_cases hg0 : g = 0
  · subst hg0
    simp
  · have habs : |g| ≠ 0 := abs_ne_zero.mpr hg0
    have hls' : (l / s ^ 2 : ℝ) ≠ 0 := ne_of_gt hls
    have hD : ((l / s ^ 2) * |g| : ℝ) ≠ 0 := mul_ne_zero hls' habs
    rw [abs_mul, abs_of_pos hls]
    field_simp

/-! ## D. Level flight on the declared polar -/

/-- Drag of the declared parabolic polar `CD = CD0 + k * CL ^ 2` at speed `V` and lift
coefficient `CL`, for air density `ρ` and wing area `S`:
`D = ρ * V ^ 2 / 2 * S * (CD0 + k * CL ^ 2)`. -/
noncomputable def polarDrag (ρ S CD0 k CL V : ℝ) : ℝ :=
  ρ * V ^ 2 / 2 * S * (CD0 + k * CL ^ 2)

/-- Lift coefficient required for level flight `L = W` at speed `V`: `CL = 2 * W / (ρ * V ^ 2 * S)`;
with the convention `x / 0 = 0` it is `0` when `ρ * V ^ 2 * S = 0`. -/
noncomputable def levelLiftCoeff (W ρ S V : ℝ) : ℝ :=
  2 * W / (ρ * V ^ 2 * S)

/-- Parasite-drag factor `a = ρ * S * CD0 / 2`: the zero-lift drag at speed `V` is `a * V ^ 2`. -/
noncomputable def parasiteDragFactor (ρ S CD0 : ℝ) : ℝ :=
  ρ * S * CD0 / 2

/-- Induced-drag factor `b = 2 * k * W ^ 2 / (ρ * S)`: the drag due to lift in level flight at speed
`V` is `b / V ^ 2`. With the convention `x / 0 = 0`, `b = 0` when `ρ * S = 0`. -/
noncomputable def inducedDragFactor (W ρ S k : ℝ) : ℝ :=
  2 * k * W ^ 2 / (ρ * S)

/-- Level-flight drag `D(V) = a * V ^ 2 + b / V ^ 2` of the declared polar; with the convention
`x / 0 = 0` it is the meaningless value `0` at `V = 0`. -/
noncomputable def levelDrag (W ρ S CD0 k V : ℝ) : ℝ :=
  parasiteDragFactor ρ S CD0 * V ^ 2 + inducedDragFactor W ρ S k / V ^ 2

/-- For `ρ, S, V ≠ 0`, at the level-flight lift coefficient the lift `ρ * V ^ 2 / 2 * S * CL` equals
the weight. -/
lemma lift_levelLiftCoeff {ρ S V : ℝ} (hρ : ρ ≠ 0) (hS : S ≠ 0) (hV : V ≠ 0) (W : ℝ) :
    ρ * V ^ 2 / 2 * S * levelLiftCoeff W ρ S V = W := by
  have hV2 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV
  have hden : ρ * V ^ 2 * S ≠ 0 := mul_ne_zero (mul_ne_zero hρ hV2) hS
  unfold levelLiftCoeff
  field_simp

/-- Imposing level flight with thrust along the velocity: for `ρ, S, V ≠ 0`, if the lift
`ρ * V ^ 2 / 2 * S * CL` equals the weight `W`, the polar drag is `D(V) = a * V ^ 2 + b / V ^ 2`. -/
lemma polarDrag_eq_levelDrag {W ρ S CD0 k CL V : ℝ} (hρ : ρ ≠ 0) (hS : S ≠ 0) (hV : V ≠ 0)
    (hL : ρ * V ^ 2 / 2 * S * CL = W) :
    polarDrag ρ S CD0 k CL V = levelDrag W ρ S CD0 k V := by
  have hV2 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV
  have hden : ρ * V ^ 2 * S ≠ 0 := mul_ne_zero (mul_ne_zero hρ hV2) hS
  have hρS : ρ * S ≠ 0 := mul_ne_zero hρ hS
  have hCL : CL = 2 * W / (ρ * V ^ 2 * S) := by
    rw [eq_div_iff hden]
    linear_combination 2 * hL
  rw [hCL]
  unfold polarDrag levelDrag parasiteDragFactor inducedDragFactor
  field_simp

/-- The parasite-drag factor is positive for `ρ, S, CD0 > 0`. -/
lemma parasiteDragFactor_pos {ρ S CD0 : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hCD0 : 0 < CD0) :
    0 < parasiteDragFactor ρ S CD0 := by
  unfold parasiteDragFactor
  positivity

/-- The induced-drag factor is positive for `W ≠ 0` and `ρ, S, k > 0`. A fact about the formula:
`b = 2 * k * W ^ 2 / (ρ * S)` depends on `W` only through `W ^ 2`. -/
lemma inducedDragFactor_pos {W ρ S k : ℝ} (hW : W ≠ 0) (hρ : 0 < ρ) (hS : 0 < S) (hk : 0 < k) :
    0 < inducedDragFactor W ρ S k := by
  unfold inducedDragFactor
  positivity

private lemma two_sqrt_mul_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  have e1 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have e2 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have e4 : 2 * Real.sqrt x * Real.sqrt y = 2 * Real.sqrt (x * y) := by
    rw [mul_assoc, ← Real.sqrt_mul hx]
  have h := sq_nonneg (Real.sqrt x - Real.sqrt y)
  rw [sub_sq, e1, e2, e4] at h
  linarith

private lemma two_sqrt_mul_eq_add_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x + y = 2 * Real.sqrt (x * y) ↔ x = y := by
  constructor
  · intro h
    have e1 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
    have e2 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
    have e4 : 2 * Real.sqrt x * Real.sqrt y = 2 * Real.sqrt (x * y) := by
      rw [mul_assoc, ← Real.sqrt_mul hx]
    have h0 : (Real.sqrt x - Real.sqrt y) ^ 2 = 0 := by
      have hexp : (Real.sqrt x - Real.sqrt y) ^ 2 = x + y - 2 * Real.sqrt (x * y) := by
        rw [sub_sq, e1, e2, e4]
        ring
      rw [hexp, h]
      ring
    have heq : Real.sqrt x = Real.sqrt y := sub_eq_zero.mp (sq_eq_zero_iff.mp h0)
    have hsq := congrArg (· ^ 2) heq
    rw [e1, e2] at hsq
    exact hsq
  · intro hxy
    subst hxy
    rw [Real.sqrt_mul_self hx]
    ring

/-! ## E. Minimum drag -/

/-- Minimum-drag speed `V_md = √(√(b / a))`. For positive weight and `ρ, S, CD0, k > 0` it is the
unique positive speed of least level-flight drag (`levelDrag_eq_two_sqrt_iff_eq_minDragSpeed`). As a
formula it is the positive root of `V ^ 4 = b / a` whenever `W ≠ 0` and `ρ, S, CD0, k > 0`
(`minDragSpeed_pos`, `minDragSpeed_pow_four`). If `ρ`, `S`, `CD0`, `k` or `W` is `0` (or
`b / a < 0`), the conventions `x / 0 = 0` and `√x = 0` for `x ≤ 0` give the value `0`, which is not
a positive speed: with `ρ, S > 0` and `CD0, k ≥ 0` the drag then has no minimum over positive speeds
when exactly one of its two terms vanishes, and every positive speed is a minimizer when both
vanish. -/
noncomputable def minDragSpeed (W ρ S CD0 k : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0))

/-- Arithmetic-geometric mean bound: for `ρ, S > 0` and `CD0, k ≥ 0`, at every nonzero speed
`2 * √(a * b) ≤ D(V)`. -/
lemma two_sqrt_le_levelDrag {W ρ S CD0 k V : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hCD0 : 0 ≤ CD0)
    (hk : 0 ≤ k) (hV : V ≠ 0) :
    2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k) ≤
      levelDrag W ρ S CD0 k V := by
  have ha : 0 ≤ parasiteDragFactor ρ S CD0 := by unfold parasiteDragFactor; positivity
  have hb : 0 ≤ inducedDragFactor W ρ S k := by unfold inducedDragFactor; positivity
  have hx : 0 ≤ parasiteDragFactor ρ S CD0 * V ^ 2 := by positivity
  have hy : 0 ≤ inducedDragFactor W ρ S k / V ^ 2 := by positivity
  have hxy : (parasiteDragFactor ρ S CD0 * V ^ 2) * (inducedDragFactor W ρ S k / V ^ 2)
      = parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k := by
    field_simp
  have h := two_sqrt_mul_le_add hx hy
  rw [hxy] at h
  unfold levelDrag
  exact h

/-- For `ρ, S, CD0 > 0`, `k ≥ 0` and `V ≠ 0`, equality in the bound holds exactly when
`V ^ 4 = b / a`. -/
lemma levelDrag_eq_two_sqrt_iff {W ρ S CD0 k V : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hCD0 : 0 < CD0)
    (hk : 0 ≤ k) (hV : V ≠ 0) :
    levelDrag W ρ S CD0 k V =
        2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k) ↔
      V ^ 4 = inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0 := by
  have ha : 0 < parasiteDragFactor ρ S CD0 := parasiteDragFactor_pos hρ hS hCD0
  have hb : 0 ≤ inducedDragFactor W ρ S k := by unfold inducedDragFactor; positivity
  have hx : 0 ≤ parasiteDragFactor ρ S CD0 * V ^ 2 := by positivity
  have hy : 0 ≤ inducedDragFactor W ρ S k / V ^ 2 := by positivity
  have hV2 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV
  have hxy : (parasiteDragFactor ρ S CD0 * V ^ 2) * (inducedDragFactor W ρ S k / V ^ 2)
      = parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k := by
    field_simp
  have h := two_sqrt_mul_eq_add_iff hx hy
  rw [hxy] at h
  unfold levelDrag
  rw [h]
  constructor
  · intro huv
    rw [eq_div_iff ha.ne']
    have huv' : (parasiteDragFactor ρ S CD0 * V ^ 2) * V ^ 2
        = inducedDragFactor W ρ S k := by
      rw [huv, div_mul_cancel₀ _ hV2]
    calc V ^ 4 * parasiteDragFactor ρ S CD0
        = (parasiteDragFactor ρ S CD0 * V ^ 2) * V ^ 2 := by ring
      _ = inducedDragFactor W ρ S k := huv'
  · intro h4
    have hb_eq : inducedDragFactor W ρ S k
        = parasiteDragFactor ρ S CD0 * V ^ 4 := by
      rw [h4, mul_div_cancel₀ _ ha.ne']
    rw [hb_eq, eq_div_iff hV2]
    ring

/-- Identity for the formula `minDragSpeed`: for `W ≠ 0` and `ρ, S, CD0, k > 0` it solves
`V ^ 4 = b / a`. It depends on `W` only through `W ^ 2`. -/
lemma minDragSpeed_pow_four {W ρ S CD0 k : ℝ} (hW : W ≠ 0) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) :
    minDragSpeed W ρ S CD0 k ^ 4 = inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0 := by
  have ht : 0 ≤ inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0 :=
    (div_pos (inducedDragFactor_pos hW hρ hS hk) (parasiteDragFactor_pos hρ hS hCD0)).le
  unfold minDragSpeed
  have h1 : (Real.sqrt (Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0))) ^ 2
      = Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  calc (Real.sqrt (Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0))) ^ 4
      = ((Real.sqrt (Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0))) ^ 2)
          ^ 2 := by
        ring
    _ = (Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0)) ^ 2 := by rw [h1]
    _ = inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0 := Real.sq_sqrt ht

/-- The formula `minDragSpeed` is positive for `W ≠ 0` and `ρ, S, CD0, k > 0`; it depends on `W`
only through `W ^ 2`. -/
lemma minDragSpeed_pos {W ρ S CD0 k : ℝ} (hW : W ≠ 0) (hρ : 0 < ρ) (hS : 0 < S) (hCD0 : 0 < CD0)
    (hk : 0 < k) : 0 < minDragSpeed W ρ S CD0 k := by
  have ha := parasiteDragFactor_pos hρ hS hCD0
  have hb := inducedDragFactor_pos hW hρ hS hk
  unfold minDragSpeed
  rw [Real.sqrt_pos, Real.sqrt_pos]
  exact div_pos hb ha

/-- For positive weight and `ρ, S, CD0, k > 0`, among positive speeds the bound is attained
exactly at the minimum-drag speed. -/
lemma levelDrag_eq_two_sqrt_iff_eq_minDragSpeed {W ρ S CD0 k V : ℝ} (hW : 0 < W) (hρ : 0 < ρ)
    (hS : 0 < S) (hCD0 : 0 < CD0) (hk : 0 < k) (hV : 0 < V) :
    levelDrag W ρ S CD0 k V =
        2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k) ↔
      V = minDragSpeed W ρ S CD0 k := by
  have ha : 0 < parasiteDragFactor ρ S CD0 := parasiteDragFactor_pos hρ hS hCD0
  have hb : 0 ≤ inducedDragFactor W ρ S k := by unfold inducedDragFactor; positivity
  have ht : 0 ≤ inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0 :=
    div_nonneg hb ha.le
  rw [levelDrag_eq_two_sqrt_iff hρ hS hCD0 hk.le hV.ne']
  unfold minDragSpeed
  constructor
  · intro h4eq
    have h4 : V ^ 4 = (V ^ 2) ^ 2 := by ring
    have hsq2 : (V ^ 2) ^ 2 =
        (Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0)) ^ 2 := by
      rw [← h4, h4eq, Real.sq_sqrt ht]
    have hsq : V ^ 2
        = Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0) := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
      · exact h
      · have hV2nn : 0 ≤ V ^ 2 := sq_nonneg V
        have htnn :=
          Real.sqrt_nonneg (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0)
        linarith
    have hsqV : V ^ 2 =
        (Real.sqrt (Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0))) ^ 2 := by
      rw [hsq, Real.sq_sqrt (Real.sqrt_nonneg _)]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqV with h | h
    · exact h
    · have hs := Real.sqrt_nonneg
        (Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0))
      linarith
  · intro hVeq
    rw [hVeq]
    have hmd := minDragSpeed_pow_four hW.ne' hρ hS hCD0 hk
    unfold minDragSpeed at hmd
    exact hmd

/-- For positive weight and `ρ, S, CD0, k > 0`, the least level-flight drag over positive speeds
is `2 * √(a * b)`. -/
lemma isLeast_levelDrag {W ρ S CD0 k : ℝ} (hW : 0 < W) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) :
    IsLeast (levelDrag W ρ S CD0 k '' Set.Ioi 0)
      (2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k)) := by
  constructor
  · have hmd := minDragSpeed_pos hW.ne' hρ hS hCD0 hk
    have hmem : levelDrag W ρ S CD0 k (minDragSpeed W ρ S CD0 k)
        = 2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k) :=
      (levelDrag_eq_two_sqrt_iff_eq_minDragSpeed hW hρ hS hCD0 hk hmd).mpr rfl
    exact ⟨minDragSpeed W ρ S CD0 k, hmd, hmem⟩
  · intro y hy
    rcases hy with ⟨V, hVmem, rfl⟩
    have hV : 0 < V := hVmem
    exact two_sqrt_le_levelDrag hρ hS hCD0.le hk.le hV.ne'

/-- Engineering form of the bound, an identity for `ρ, S ≠ 0` and all other parameters:
`2 * √(a * b) = 2 * |W| * √(CD0 * k)`. For positive weight and `ρ, S, CD0, k > 0` it is the minimum
drag (`isLeast_levelDrag`); in level flight the lift equals the weight `W`, so the greatest
lift-to-drag ratio is `W / (2 * W * √(CD0 * k)) = 1 / (2 * √(CD0 * k))`. That consequence needs
`W > 0`: for `W < 0` the lift is negative and the ratio at minimum drag is
`-1 / (2 * √(CD0 * k))`. -/
lemma two_sqrt_mul_dragFactor_eq {W ρ S CD0 k : ℝ} (hρ : ρ ≠ 0) (hS : S ≠ 0) :
    2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k) =
      2 * |W| * Real.sqrt (CD0 * k) := by
  have hρS : ρ * S ≠ 0 := mul_ne_zero hρ hS
  have hab : parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k
      = (CD0 * k) * W ^ 2 := by
    unfold parasiteDragFactor inducedDragFactor
    field_simp
  rw [hab]
  by_cases hc : 0 ≤ CD0 * k
  · rw [Real.sqrt_mul hc, Real.sqrt_sq_eq_abs]
    ring
  · push Not at hc
    have h1 : (CD0 * k) * W ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc.le (sq_nonneg W)
    rw [Real.sqrt_eq_zero_of_nonpos h1, Real.sqrt_eq_zero_of_nonpos hc.le]
    ring

/-! ## F. The stall-validity interval -/

/-- Stall speed `V_s = √(2 * W / (ρ * S * CLmax))` for the polar's maximum lift coefficient
`CLmax`. The physical regime is `W, ρ, S, CLmax > 0`; for `W ≤ 0` (with `ρ, S, CLmax > 0`) the
radicand is not positive and `Real.sqrt` returns the meaningless value `0`, so the stall results
assume `0 < W`. -/
noncomputable def stallSpeed (W ρ S CLmax : ℝ) : ℝ :=
  Real.sqrt (2 * W / (ρ * S * CLmax))

/-- The stall-validity interval: for `W, ρ, S, CLmax > 0`, at a positive speed the level-flight lift
coefficient is at most `CLmax` exactly when the speed is at least the stall speed. -/
lemma levelLiftCoeff_le_iff_stallSpeed_le {W ρ S CLmax V : ℝ} (hW : 0 < W) (hρ : 0 < ρ)
    (hS : 0 < S) (hCL : 0 < CLmax) (hV : 0 < V) :
    levelLiftCoeff W ρ S V ≤ CLmax ↔ stallSpeed W ρ S CLmax ≤ V := by
  have hd1 : 0 < ρ * V ^ 2 * S := by positivity
  have hd2 : 0 < ρ * S * CLmax := by positivity
  have hs : 0 ≤ stallSpeed W ρ S CLmax := Real.sqrt_nonneg _
  have hsq : stallSpeed W ρ S CLmax ^ 2 = 2 * W / (ρ * S * CLmax) :=
    Real.sq_sqrt (div_pos (mul_pos two_pos hW) hd2).le
  rw [← sq_le_sq₀ hs hV.le, hsq]
  unfold levelLiftCoeff
  rw [div_le_iff₀ hd1, div_le_iff₀ hd2]
  have heq : CLmax * (ρ * V ^ 2 * S) = V ^ 2 * (ρ * S * CLmax) := by ring
  rw [heq]

/-- Subject to the stall-validity interval: for `W > 0` and `ρ, S, CD0, k, CLmax > 0`, some positive
speed with lift coefficient at most `CLmax` attains the bound `2 * √(a * b)` exactly when the stall
speed is at most the minimum-drag speed. -/
lemma exists_levelDrag_eq_two_sqrt_iff {W ρ S CD0 k CLmax : ℝ} (hW : 0 < W) (hρ : 0 < ρ)
    (hS : 0 < S) (hCD0 : 0 < CD0) (hk : 0 < k) (hCL : 0 < CLmax) :
    (∃ V, 0 < V ∧ levelLiftCoeff W ρ S V ≤ CLmax ∧
        levelDrag W ρ S CD0 k V =
          2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k)) ↔
      stallSpeed W ρ S CLmax ≤ minDragSpeed W ρ S CD0 k := by
  constructor
  · rintro ⟨V, hV, hadm, hD⟩
    have hVeq : V = minDragSpeed W ρ S CD0 k :=
      (levelDrag_eq_two_sqrt_iff_eq_minDragSpeed hW hρ hS hCD0 hk hV).mp hD
    have hVs : stallSpeed W ρ S CLmax ≤ V :=
      (levelLiftCoeff_le_iff_stallSpeed_le hW hρ hS hCL hV).mp hadm
    rw [hVeq] at hVs
    exact hVs
  · intro hle
    have hmd := minDragSpeed_pos hW.ne' hρ hS hCD0 hk
    refine ⟨minDragSpeed W ρ S CD0 k, hmd, ?_, ?_⟩
    · exact (levelLiftCoeff_le_iff_stallSpeed_le hW hρ hS hCL hmd).mpr hle
    · exact (levelDrag_eq_two_sqrt_iff_eq_minDragSpeed hW hρ hS hCD0 hk hmd).mpr rfl

/-- An unconstrained minimizer below the stall speed is not an operating point: for `W > 0` and
`ρ, S, CD0, k, CLmax > 0`, if the minimum-drag speed is below the stall speed, every positive speed
with lift coefficient at most `CLmax` has drag strictly above `2 * √(a * b)`. -/
lemma two_sqrt_lt_levelDrag_of_minDragSpeed_lt_stallSpeed {W ρ S CD0 k CLmax V : ℝ}
    (hW : 0 < W) (hρ : 0 < ρ) (hS : 0 < S) (hCD0 : 0 < CD0) (hk : 0 < k) (hCL : 0 < CLmax)
    (hmd : minDragSpeed W ρ S CD0 k < stallSpeed W ρ S CLmax) (hV : 0 < V)
    (hadm : levelLiftCoeff W ρ S V ≤ CLmax) :
    2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k) <
      levelDrag W ρ S CD0 k V := by
  have hVs : stallSpeed W ρ S CLmax ≤ V :=
    (levelLiftCoeff_le_iff_stallSpeed_le hW hρ hS hCL hV).mp hadm
  have hne : V ≠ minDragSpeed W ρ S CD0 k := ne_of_gt (lt_of_lt_of_le hmd hVs)
  have hle : 2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k)
      ≤ levelDrag W ρ S CD0 k V :=
    two_sqrt_le_levelDrag hρ hS hCD0.le hk.le hV.ne'
  have hiff : levelDrag W ρ S CD0 k V
        = 2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k) ↔
      V = minDragSpeed W ρ S CD0 k :=
    levelDrag_eq_two_sqrt_iff_eq_minDragSpeed hW hρ hS hCD0 hk hV
  have hDne : levelDrag W ρ S CD0 k V
      ≠ 2 * Real.sqrt (parasiteDragFactor ρ S CD0 * inducedDragFactor W ρ S k) := by
    intro hcon
    exact hne (hiff.mp hcon)
  exact lt_of_le_of_ne hle (Ne.symm hDne)

/-- For `W > 0` and `ρ, S, CD0, k, CLmax > 0`, the stall speed exceeds the minimum-drag speed
exactly when the lift coefficient at minimum drag, `√(CD0 / k)`, exceeds `CLmax`. -/
lemma minDragSpeed_lt_stallSpeed_iff {W ρ S CD0 k CLmax : ℝ} (hW : 0 < W) (hρ : 0 < ρ)
    (hS : 0 < S) (hCD0 : 0 < CD0) (hk : 0 < k) (hCL : 0 < CLmax) :
    minDragSpeed W ρ S CD0 k < stallSpeed W ρ S CLmax ↔ CLmax < Real.sqrt (CD0 / k) := by
  have ha := parasiteDragFactor_pos hρ hS hCD0
  have hb := inducedDragFactor_pos hW.ne' hρ hS hk
  have hsqrt_nonneg : 0 ≤ Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0) :=
    Real.sqrt_nonneg _
  have htpos : 0 < 2 * W / (ρ * S * CLmax) := by positivity
  unfold minDragSpeed stallSpeed
  rw [Real.sqrt_lt_sqrt_iff hsqrt_nonneg, Real.sqrt_lt' htpos, Real.lt_sqrt hCL.le]
  have hρS : 0 < ρ * S := mul_pos hρ hS
  have e_ba : inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0
      = 4 * k * W ^ 2 / ((ρ * S) ^ 2 * CD0) := by
    unfold parasiteDragFactor inducedDragFactor
    have h1 : ρ * S ≠ 0 := ne_of_gt hρS
    have h2 : ρ * S * CD0 / 2 ≠ 0 := ne_of_gt (by positivity)
    have h3 : (ρ * S) ^ 2 * CD0 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  have e_t : (2 * W / (ρ * S * CLmax)) ^ 2
      = 4 * W ^ 2 / ((ρ * S) ^ 2 * CLmax ^ 2) := by
    have h1 : ρ * S * CLmax ≠ 0 := ne_of_gt (by positivity)
    have h2 : (ρ * S) ^ 2 * CLmax ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  have hD1 : 0 < (ρ * S) ^ 2 * CD0 := by positivity
  have hD2 : 0 < (ρ * S) ^ 2 * CLmax ^ 2 := by positivity
  have hF : 0 < 4 * W ^ 2 * (ρ * S) ^ 2 := by positivity
  have hred : (4 * k * W ^ 2 / ((ρ * S) ^ 2 * CD0)
      < 4 * W ^ 2 / ((ρ * S) ^ 2 * CLmax ^ 2))
      ↔ (4 * k * W ^ 2 * ((ρ * S) ^ 2 * CLmax ^ 2)
        < 4 * W ^ 2 * ((ρ * S) ^ 2 * CD0)) := by
    rw [div_lt_iff₀ hD1, div_mul_eq_mul_div, lt_div_iff₀ hD2]
  have hnum1 : (4 * k * W ^ 2 * ((ρ * S) ^ 2 * CLmax ^ 2)
      < 4 * W ^ 2 * ((ρ * S) ^ 2 * CD0)) ↔ CLmax ^ 2 < CD0 / k := by
    have r1 : 4 * k * W ^ 2 * ((ρ * S) ^ 2 * CLmax ^ 2)
        = (k * CLmax ^ 2) * (4 * W ^ 2 * (ρ * S) ^ 2) := by ring
    have r2 : 4 * W ^ 2 * ((ρ * S) ^ 2 * CD0)
        = CD0 * (4 * W ^ 2 * (ρ * S) ^ 2) := by ring
    rw [r1, r2, mul_lt_mul_iff_of_pos_right hF, lt_div_iff₀ hk]
    have hcomm : k * CLmax ^ 2 = CLmax ^ 2 * k := by ring
    rw [hcomm]
  rw [e_ba, e_t, hred]
  exact hnum1

/-! ## G. Isothermal-layer density as the density input -/

/-- The density of the isothermal layer at any height `z` is an admissible density input: for
`ρ0, Rs, T, S > 0` and `CD0, k ≥ 0`, the level-flight drag at every nonzero speed is at least
`2 * √(a * b)` evaluated at that density. -/
lemma two_sqrt_le_levelDrag_isothermalDensity {ρ0 Rs T S CD0 k V : ℝ} (hρ0 : 0 < ρ0)
    (hRs : 0 < Rs) (hT : 0 < T) (hS : 0 < S) (hCD0 : 0 ≤ CD0) (hk : 0 ≤ k) (hV : V ≠ 0)
    (W g z : ℝ) :
    2 * Real.sqrt (parasiteDragFactor (isothermalDensity ρ0 g Rs T z) S CD0 *
        inducedDragFactor W (isothermalDensity ρ0 g Rs T z) S k) ≤
      levelDrag W (isothermalDensity ρ0 g Rs T z) S CD0 k V := by
  exact two_sqrt_le_levelDrag (isothermalDensity_pos hρ0 hRs hT g z) hS hCD0 hk hV

/-! ## H. Power required -/

/-- Power required in steady level flight on the declared polar: the thrust power
`P(V) = D(V) * V`, the rate at which the thrust `T = D` works along the flight path. It is the
power delivered by the thrust, not the shaft power of the engine (`shaftPowerRequired`). -/
noncomputable def levelPower (W ρ S CD0 k V : ℝ) : ℝ :=
  levelDrag W ρ S CD0 k V * V

/-- The power required is `P(V) = a * V ^ 3 + b / V`. As an identity of the formulas it holds at
every speed; at `V = 0` both sides are the meaningless value `0`. -/
lemma levelPower_eq (W ρ S CD0 k V : ℝ) :
    levelPower W ρ S CD0 k V =
      parasiteDragFactor ρ S CD0 * V ^ 3 + inducedDragFactor W ρ S k / V := by
  unfold levelPower levelDrag
  by_cases hV : V = 0
  · subst hV
    simp
  · have hV2 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV
    field_simp

/-- Imposing level flight with thrust along the velocity: for `ρ, S, V ≠ 0`, if the lift
`ρ * V ^ 2 / 2 * S * CL` equals the weight `W`, the thrust power `D * V` of the declared polar is
the power required `P(V)`. -/
lemma polarDrag_mul_eq_levelPower {W ρ S CD0 k CL V : ℝ} (hρ : ρ ≠ 0) (hS : S ≠ 0) (hV : V ≠ 0)
    (hL : ρ * V ^ 2 / 2 * S * CL = W) :
    polarDrag ρ S CD0 k CL V * V = levelPower W ρ S CD0 k V := by
  rw [polarDrag_eq_levelDrag hρ hS hV hL]
  rfl

/-- At every nonzero speed the power required has derivative
`P'(V) = 3 * a * V ^ 2 - b / V ^ 2`. -/
lemma hasDerivAt_levelPower {W ρ S CD0 k V : ℝ} (hV : V ≠ 0) :
    HasDerivAt (levelPower W ρ S CD0 k)
      (3 * parasiteDragFactor ρ S CD0 * V ^ 2 - inducedDragFactor W ρ S k / V ^ 2) V := by
  have hfun : levelPower W ρ S CD0 k
      = fun x => parasiteDragFactor ρ S CD0 * x ^ 3 + inducedDragFactor W ρ S k / x :=
    funext (fun x => levelPower_eq W ρ S CD0 k x)
  rw [hfun]
  have hV2 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV
  have h1 : HasDerivAt (fun x : ℝ => parasiteDragFactor ρ S CD0 * x ^ 3)
      (3 * parasiteDragFactor ρ S CD0 * V ^ 2) V := by
    have h := (hasDerivAt_pow 3 V).const_mul (parasiteDragFactor ρ S CD0)
    norm_num at h
    have hrw : parasiteDragFactor ρ S CD0 * (3 * V ^ 2)
        = 3 * parasiteDragFactor ρ S CD0 * V ^ 2 := by ring
    rw [hrw] at h
    exact h
  have h2 : HasDerivAt (fun x : ℝ => inducedDragFactor W ρ S k / x)
      (-(inducedDragFactor W ρ S k / V ^ 2)) V := by
    have h := (hasDerivAt_inv hV).const_mul (inducedDragFactor W ρ S k)
    have hfeq : (fun x : ℝ => inducedDragFactor W ρ S k * x⁻¹)
        = fun x : ℝ => inducedDragFactor W ρ S k / x := by
      funext x
      rw [div_eq_mul_inv]
    rw [hfeq] at h
    have hrw : inducedDragFactor W ρ S k * (-(V ^ 2)⁻¹)
        = -(inducedDragFactor W ρ S k / V ^ 2) := by
      field_simp
    rw [hrw] at h
    exact h
  have h := h1.add h2
  have hrw : 3 * parasiteDragFactor ρ S CD0 * V ^ 2 + -(inducedDragFactor W ρ S k / V ^ 2)
      = 3 * parasiteDragFactor ρ S CD0 * V ^ 2 - inducedDragFactor W ρ S k / V ^ 2 := by ring
  rw [hrw] at h
  exact h

/-! ## I. Minimum power -/

private lemma levelPower_sub_eq {W ρ S CD0 k U V : ℝ} (hU : U ≠ 0) (hV : V ≠ 0)
    (hb : inducedDragFactor W ρ S k = 3 * parasiteDragFactor ρ S CD0 * V ^ 4) :
    levelPower W ρ S CD0 k U - levelPower W ρ S CD0 k V =
      parasiteDragFactor ρ S CD0 * (U - V) ^ 2 * (U ^ 2 + 2 * U * V + 3 * V ^ 2) / U := by
  have hU2 : U ^ 2 ≠ 0 := pow_ne_zero 2 hU
  have hV2 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV
  rw [levelPower_eq, levelPower_eq, hb]
  field_simp
  ring

/-- First-order condition, both ways: for `ρ, S, CD0 > 0`, a positive speed minimizes the power
required over all positive speeds exactly when `V ^ 4 = b / (3 * a)`. No sign of `k` or `W` is
needed: for `b ≤ 0` both sides are false. -/
lemma isMinOn_levelPower_iff {W ρ S CD0 k V : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hCD0 : 0 < CD0)
    (hV : 0 < V) :
    IsMinOn (levelPower W ρ S CD0 k) (Set.Ioi 0) V ↔
      V ^ 4 = inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0) := by
  have ha := parasiteDragFactor_pos hρ hS hCD0
  have hV0 : V ≠ 0 := ne_of_gt hV
  have hV20 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV0
  have h3a : (3 : ℝ) * parasiteDragFactor ρ S CD0 ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt ha)
  constructor
  · intro h
    have hloc : IsLocalMin (levelPower W ρ S CD0 k) V := h.isLocalMin (Ioi_mem_nhds hV)
    have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_levelPower hV0)
    rw [sub_eq_zero] at h0
    rw [eq_div_iff h3a]
    have hmul := congrArg (fun x => x * V ^ 2) h0
    rw [div_mul_cancel₀ _ hV20] at hmul
    linear_combination hmul
  · intro hV4
    have hb : inducedDragFactor W ρ S k = 3 * parasiteDragFactor ρ S CD0 * V ^ 4 := by
      rw [eq_div_iff h3a] at hV4
      linear_combination -hV4
    rw [isMinOn_iff]
    intro U hU
    have hUpos : 0 < U := hU
    have hU0 : U ≠ 0 := ne_of_gt hUpos
    have hdiff := levelPower_sub_eq hU0 hV0 hb
    have hnonneg : 0 ≤ parasiteDragFactor ρ S CD0 * (U - V) ^ 2
        * (U ^ 2 + 2 * U * V + 3 * V ^ 2) / U := by
      apply div_nonneg _ hUpos.le
      apply mul_nonneg _ _
      · exact mul_nonneg ha.le (sq_nonneg _)
      · have hpos : 0 < U ^ 2 + 2 * U * V + 3 * V ^ 2 := by positivity
        exact hpos.le
    linarith [hdiff, hnonneg]

/-- Minimum-power speed `V_mp = √(√(b / (3 * a)))`. For positive weight and `ρ, S, CD0, k > 0` it is
the unique positive speed of least power required (`levelPower_minPowerSpeed_lt`). As a formula it
is the positive root of `V ^ 4 = b / (3 * a)` whenever `W ≠ 0` and `ρ, S, CD0, k > 0`
(`minPowerSpeed_pos`, `minPowerSpeed_pow_four`). If `ρ`, `S`, `CD0`, `k` or `W` is `0` (or
`b / (3 * a) < 0`), the conventions `x / 0 = 0` and `√x = 0` for `x ≤ 0` give the value `0`, which
is not a positive speed. -/
noncomputable def minPowerSpeed (W ρ S CD0 k : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0)))

/-- The formula `minPowerSpeed` is positive for `W ≠ 0` and `ρ, S, CD0, k > 0`; it depends on `W`
only through `W ^ 2`. -/
lemma minPowerSpeed_pos {W ρ S CD0 k : ℝ} (hW : W ≠ 0) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) : 0 < minPowerSpeed W ρ S CD0 k := by
  have ha := parasiteDragFactor_pos hρ hS hCD0
  have hb := inducedDragFactor_pos hW hρ hS hk
  unfold minPowerSpeed
  rw [Real.sqrt_pos, Real.sqrt_pos]
  exact div_pos hb (mul_pos (by norm_num) ha)

/-- Identity for the formula `minPowerSpeed`: for `W ≠ 0` and `ρ, S, CD0, k > 0` it solves
`V ^ 4 = b / (3 * a)`. -/
lemma minPowerSpeed_pow_four {W ρ S CD0 k : ℝ} (hW : W ≠ 0) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) :
    minPowerSpeed W ρ S CD0 k ^ 4 =
      inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0) := by
  have ht : 0 ≤ inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0) :=
    (div_pos (inducedDragFactor_pos hW hρ hS hk)
      (mul_pos (by norm_num) (parasiteDragFactor_pos hρ hS hCD0))).le
  unfold minPowerSpeed
  have h1 :
      (Real.sqrt (Real.sqrt (inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0)))) ^ 2
      = Real.sqrt (inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0)) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  calc (Real.sqrt (Real.sqrt (inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0)))) ^ 4
      = ((Real.sqrt (Real.sqrt (inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0)))) ^ 2)
          ^ 2 := by
        ring
    _ = (Real.sqrt (inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0))) ^ 2 := by rw [h1]
    _ = inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0) := Real.sq_sqrt ht

/-- For positive weight and `ρ, S, CD0, k > 0`, every positive speed other than `V_mp` needs
strictly more power: `V_mp` is the unique positive minimizer. -/
lemma levelPower_minPowerSpeed_lt {W ρ S CD0 k V : ℝ} (hW : 0 < W) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) (hV : 0 < V) (hne : V ≠ minPowerSpeed W ρ S CD0 k) :
    levelPower W ρ S CD0 k (minPowerSpeed W ρ S CD0 k) < levelPower W ρ S CD0 k V := by
  have hW0 : W ≠ 0 := ne_of_gt hW
  have ha := parasiteDragFactor_pos hρ hS hCD0
  have hmp := minPowerSpeed_pos hW0 hρ hS hCD0 hk
  have hmp4 := minPowerSpeed_pow_four hW0 hρ hS hCD0 hk
  have h3a : (3 : ℝ) * parasiteDragFactor ρ S CD0 ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt ha)
  have hb : inducedDragFactor W ρ S k
      = 3 * parasiteDragFactor ρ S CD0 * minPowerSpeed W ρ S CD0 k ^ 4 := by
    rw [eq_div_iff h3a] at hmp4
    linear_combination -hmp4
  have hdiff := levelPower_sub_eq (ne_of_gt hV) (ne_of_gt hmp) hb
  have hsub : V - minPowerSpeed W ρ S CD0 k ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hpos : 0 < parasiteDragFactor ρ S CD0 * (V - minPowerSpeed W ρ S CD0 k) ^ 2
      * (V ^ 2 + 2 * V * minPowerSpeed W ρ S CD0 k
        + 3 * minPowerSpeed W ρ S CD0 k ^ 2) / V := by
    apply div_pos _ hV
    apply mul_pos _ _
    · exact mul_pos ha (by simpa [pow_two] using mul_self_pos.mpr hsub)
    · positivity
  linarith [hdiff, hpos]

private lemma levelPower_sub_factor (W ρ S CD0 k X Y : ℝ) (hX : X ≠ 0) (hY : Y ≠ 0) :
    levelPower W ρ S CD0 k Y - levelPower W ρ S CD0 k X =
      (Y - X) * (parasiteDragFactor ρ S CD0 * (Y ^ 2 + Y * X + X ^ 2)
        - inducedDragFactor W ρ S k / (Y * X)) := by
  have hX2 : X ^ 2 ≠ 0 := pow_ne_zero 2 hX
  have hY2 : Y ^ 2 ≠ 0 := pow_ne_zero 2 hY
  have hYX : Y * X ≠ 0 := mul_ne_zero hY hX
  rw [levelPower_eq, levelPower_eq]
  field_simp
  ring

/-- For positive weight and `ρ, S, CD0, k > 0`, the least power required over positive speeds is
`P(V_mp)`. -/
lemma isLeast_levelPower {W ρ S CD0 k : ℝ} (hW : 0 < W) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) :
    IsLeast (levelPower W ρ S CD0 k '' Set.Ioi 0)
      (levelPower W ρ S CD0 k (minPowerSpeed W ρ S CD0 k)) := by
  have hW0 : W ≠ 0 := ne_of_gt hW
  have hmp := minPowerSpeed_pos hW0 hρ hS hCD0 hk
  have hmp4 := minPowerSpeed_pow_four hW0 hρ hS hCD0 hk
  have hmin : IsMinOn (levelPower W ρ S CD0 k) (Set.Ioi 0) (minPowerSpeed W ρ S CD0 k) :=
    (isMinOn_levelPower_iff hρ hS hCD0 hmp).mpr hmp4
  rw [isMinOn_iff] at hmin
  constructor
  · exact ⟨minPowerSpeed W ρ S CD0 k, hmp, rfl⟩
  · intro y hy
    obtain ⟨U, hU, rfl⟩ := hy
    exact hmin U hU

/-- For positive weight and `ρ, S, CD0, k > 0`, the power required strictly decreases with speed
on `(0, V_mp]`. -/
lemma levelPower_strictAntiOn {W ρ S CD0 k : ℝ} (hW : 0 < W) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) :
    StrictAntiOn (levelPower W ρ S CD0 k) (Set.Ioc 0 (minPowerSpeed W ρ S CD0 k)) := by
  have hW0 : W ≠ 0 := ne_of_gt hW
  have ha := parasiteDragFactor_pos hρ hS hCD0
  have hm := minPowerSpeed_pos hW0 hρ hS hCD0 hk
  have hm4 := minPowerSpeed_pow_four hW0 hρ hS hCD0 hk
  have h3a : (3 : ℝ) * parasiteDragFactor ρ S CD0 ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt ha)
  have hb : inducedDragFactor W ρ S k
      = 3 * parasiteDragFactor ρ S CD0 * minPowerSpeed W ρ S CD0 k ^ 4 := by
    rw [eq_div_iff h3a] at hm4
    linear_combination -hm4
  intro X hX Y hY hXY
  rw [Set.mem_Ioc] at hX hY
  obtain ⟨hX0, hXm⟩ := hX
  obtain ⟨hY0, hYm⟩ := hY
  have hXm' : X < minPowerSpeed W ρ S CD0 k := lt_of_lt_of_le hXY hYm
  have hkey := levelPower_sub_factor W ρ S CD0 k X Y (ne_of_gt hX0) (ne_of_gt hY0)
  rw [hb] at hkey
  have hYX : 0 < Y * X := mul_pos hY0 hX0
  have hYXm : Y * X < minPowerSpeed W ρ S CD0 k ^ 2 := by
    calc Y * X ≤ minPowerSpeed W ρ S CD0 k * X :=
          mul_le_mul_of_nonneg_right hYm hX0.le
      _ < minPowerSpeed W ρ S CD0 k * minPowerSpeed W ρ S CD0 k :=
          mul_lt_mul_of_pos_left hXm' hm
      _ = minPowerSpeed W ρ S CD0 k ^ 2 := by ring
  have hS : Y ^ 2 + Y * X + X ^ 2 < 3 * minPowerSpeed W ρ S CD0 k ^ 2 := by
    have e1 : Y ^ 2 ≤ minPowerSpeed W ρ S CD0 k ^ 2 := by nlinarith [hYm, hY0.le, hm]
    have e3 : X ^ 2 < minPowerSpeed W ρ S CD0 k ^ 2 := by nlinarith [hXm', hX0.le, hm]
    linarith [hYXm, e1, e3]
  have hSpos : 0 < Y ^ 2 + Y * X + X ^ 2 := by positivity
  have hm2pos : 0 < minPowerSpeed W ρ S CD0 k ^ 2 := by positivity
  have step1 : (Y * X) * (Y ^ 2 + Y * X + X ^ 2)
      ≤ minPowerSpeed W ρ S CD0 k ^ 2 * (Y ^ 2 + Y * X + X ^ 2) :=
    mul_le_mul_of_nonneg_right hYXm.le hSpos.le
  have step2 : minPowerSpeed W ρ S CD0 k ^ 2 * (Y ^ 2 + Y * X + X ^ 2)
      < minPowerSpeed W ρ S CD0 k ^ 2 * (3 * minPowerSpeed W ρ S CD0 k ^ 2) :=
    mul_lt_mul_of_pos_left hS hm2pos
  have hring : minPowerSpeed W ρ S CD0 k ^ 2 * (3 * minPowerSpeed W ρ S CD0 k ^ 2)
      = 3 * minPowerSpeed W ρ S CD0 k ^ 4 := by ring
  rw [hring] at step2
  have hprod : (Y ^ 2 + Y * X + X ^ 2) * (Y * X)
      < 3 * minPowerSpeed W ρ S CD0 k ^ 4 := by
    have hcomm : (Y ^ 2 + Y * X + X ^ 2) * (Y * X)
        = (Y * X) * (Y ^ 2 + Y * X + X ^ 2) := by ring
    rw [hcomm]
    linarith [step1, step2]
  have hlt : Y ^ 2 + Y * X + X ^ 2
      < 3 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X) := by
    rw [lt_div_iff₀ hYX]
    exact hprod
  have hbracket : parasiteDragFactor ρ S CD0 * (Y ^ 2 + Y * X + X ^ 2)
      - 3 * parasiteDragFactor ρ S CD0 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X) < 0 := by
    have h1 : parasiteDragFactor ρ S CD0
        * (Y ^ 2 + Y * X + X ^ 2 - 3 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X)) < 0 :=
      mul_neg_of_pos_of_neg ha (by linarith [hlt])
    have h2 : parasiteDragFactor ρ S CD0 * (Y ^ 2 + Y * X + X ^ 2)
        - 3 * parasiteDragFactor ρ S CD0 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X)
        = parasiteDragFactor ρ S CD0
          * (Y ^ 2 + Y * X + X ^ 2 - 3 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X)) := by
      ring
    rw [h2]
    exact h1
  have hmul : (Y - X) * (parasiteDragFactor ρ S CD0 * (Y ^ 2 + Y * X + X ^ 2)
      - 3 * parasiteDragFactor ρ S CD0 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith [hXY]) hbracket
  linarith [hkey, hmul]

/-- For positive weight and `ρ, S, CD0, k > 0`, the power required strictly increases with speed
on `[V_mp, ∞)`. -/
lemma levelPower_strictMonoOn {W ρ S CD0 k : ℝ} (hW : 0 < W) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) :
    StrictMonoOn (levelPower W ρ S CD0 k) (Set.Ici (minPowerSpeed W ρ S CD0 k)) := by
  have hW0 : W ≠ 0 := ne_of_gt hW
  have ha := parasiteDragFactor_pos hρ hS hCD0
  have hm := minPowerSpeed_pos hW0 hρ hS hCD0 hk
  have hm4 := minPowerSpeed_pow_four hW0 hρ hS hCD0 hk
  have h3a : (3 : ℝ) * parasiteDragFactor ρ S CD0 ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt ha)
  have hb : inducedDragFactor W ρ S k
      = 3 * parasiteDragFactor ρ S CD0 * minPowerSpeed W ρ S CD0 k ^ 4 := by
    rw [eq_div_iff h3a] at hm4
    linear_combination -hm4
  intro X hX Y hY hXY
  rw [Set.mem_Ici] at hX hY
  have hX0 : 0 < X := lt_of_lt_of_le hm hX
  have hY0 : 0 < Y := lt_of_lt_of_le hm hY
  have hkey := levelPower_sub_factor W ρ S CD0 k X Y (ne_of_gt hX0) (ne_of_gt hY0)
  rw [hb] at hkey
  have hYX : 0 < Y * X := mul_pos hY0 hX0
  have hYXm : minPowerSpeed W ρ S CD0 k ^ 2 < Y * X := by
    calc minPowerSpeed W ρ S CD0 k ^ 2
        = minPowerSpeed W ρ S CD0 k * minPowerSpeed W ρ S CD0 k := by ring
      _ ≤ minPowerSpeed W ρ S CD0 k * X := mul_le_mul_of_nonneg_left hX hm.le
      _ < Y * X := mul_lt_mul_of_pos_right (lt_of_le_of_lt hX hXY) hX0
  have hS : 3 * minPowerSpeed W ρ S CD0 k ^ 2 < Y ^ 2 + Y * X + X ^ 2 := by
    have e1 : minPowerSpeed W ρ S CD0 k ^ 2 ≤ Y ^ 2 := by nlinarith [hY, hm.le, hY0.le]
    have e3 : minPowerSpeed W ρ S CD0 k ^ 2 ≤ X ^ 2 := by nlinarith [hX, hm.le, hX0.le]
    linarith [hYXm, e1, e3]
  have hSpos : 0 < Y ^ 2 + Y * X + X ^ 2 := by positivity
  have hm2pos : 0 < minPowerSpeed W ρ S CD0 k ^ 2 := by positivity
  have step1 : minPowerSpeed W ρ S CD0 k ^ 2 * (Y ^ 2 + Y * X + X ^ 2)
      ≤ (Y * X) * (Y ^ 2 + Y * X + X ^ 2) :=
    mul_le_mul_of_nonneg_right hYXm.le hSpos.le
  have step2 : minPowerSpeed W ρ S CD0 k ^ 2 * (3 * minPowerSpeed W ρ S CD0 k ^ 2)
      < minPowerSpeed W ρ S CD0 k ^ 2 * (Y ^ 2 + Y * X + X ^ 2) :=
    mul_lt_mul_of_pos_left hS hm2pos
  have hring : minPowerSpeed W ρ S CD0 k ^ 2 * (3 * minPowerSpeed W ρ S CD0 k ^ 2)
      = 3 * minPowerSpeed W ρ S CD0 k ^ 4 := by ring
  rw [hring] at step2
  have hprod : 3 * minPowerSpeed W ρ S CD0 k ^ 4
      < (Y ^ 2 + Y * X + X ^ 2) * (Y * X) := by
    have hcomm : (Y ^ 2 + Y * X + X ^ 2) * (Y * X)
        = (Y * X) * (Y ^ 2 + Y * X + X ^ 2) := by ring
    rw [hcomm]
    linarith [step1, step2]
  have hgt : 3 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X)
      < Y ^ 2 + Y * X + X ^ 2 := by
    rw [div_lt_iff₀ hYX]
    exact hprod
  have hbracket : 0 < parasiteDragFactor ρ S CD0 * (Y ^ 2 + Y * X + X ^ 2)
      - 3 * parasiteDragFactor ρ S CD0 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X) := by
    have h1 : 0 < parasiteDragFactor ρ S CD0
        * (Y ^ 2 + Y * X + X ^ 2 - 3 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X)) :=
      mul_pos ha (by linarith [hgt])
    have h2 : parasiteDragFactor ρ S CD0 * (Y ^ 2 + Y * X + X ^ 2)
        - 3 * parasiteDragFactor ρ S CD0 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X)
        = parasiteDragFactor ρ S CD0
          * (Y ^ 2 + Y * X + X ^ 2 - 3 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X)) := by
      ring
    rw [h2]
    exact h1
  have hmul : 0 < (Y - X) * (parasiteDragFactor ρ S CD0 * (Y ^ 2 + Y * X + X ^ 2)
      - 3 * parasiteDragFactor ρ S CD0 * minPowerSpeed W ρ S CD0 k ^ 4 / (Y * X)) :=
    mul_pos (by linarith [hXY]) hbracket
  linarith [hkey, hmul]

/-! ## J. Distinct from the minimum-drag speed -/

/-- Identity for the formulas: `V_md ^ 4 = 3 * V_mp ^ 4` for `W ≠ 0` and `ρ, S, CD0, k > 0`, so
`V_mp = V_md / 3 ^ (1 / 4)`, about `0.76 * V_md`. -/
lemma minDragSpeed_pow_four_eq {W ρ S CD0 k : ℝ} (hW : W ≠ 0) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) :
    minDragSpeed W ρ S CD0 k ^ 4 = 3 * minPowerSpeed W ρ S CD0 k ^ 4 := by
  have hmd := minDragSpeed_pow_four hW hρ hS hCD0 hk
  have hmp := minPowerSpeed_pow_four hW hρ hS hCD0 hk
  have ha0 : parasiteDragFactor ρ S CD0 ≠ 0 :=
    ne_of_gt (parasiteDragFactor_pos hρ hS hCD0)
  have h3a : (3 : ℝ) * parasiteDragFactor ρ S CD0 ≠ 0 := mul_ne_zero (by norm_num) ha0
  rw [hmd, hmp]
  field_simp

/-- The minimum-power speed lies strictly below the minimum-drag speed, for `W ≠ 0` and
`ρ, S, CD0, k > 0`. -/
lemma minPowerSpeed_lt_minDragSpeed {W ρ S CD0 k : ℝ} (hW : W ≠ 0) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) :
    minPowerSpeed W ρ S CD0 k < minDragSpeed W ρ S CD0 k := by
  have hmd_pos := minDragSpeed_pos hW hρ hS hCD0 hk
  have hmp_pos := minPowerSpeed_pos hW hρ hS hCD0 hk
  have heq := minDragSpeed_pow_four_eq hW hρ hS hCD0 hk
  have hlt4 : minPowerSpeed W ρ S CD0 k ^ 4 < minDragSpeed W ρ S CD0 k ^ 4 := by
    rw [heq]
    have hpos : 0 < minPowerSpeed W ρ S CD0 k ^ 4 := by positivity
    linarith [hpos]
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  exact (pow_lt_pow_iff_left₀ hmp_pos.le hmd_pos.le h4).mp hlt4

/-- The minimum-drag speed is not power-optimal: for positive weight and `ρ, S, CD0, k > 0` the
power required there strictly exceeds the least power `P(V_mp)`. -/
lemma levelPower_minPowerSpeed_lt_minDragSpeed {W ρ S CD0 k : ℝ} (hW : 0 < W) (hρ : 0 < ρ)
    (hS : 0 < S) (hCD0 : 0 < CD0) (hk : 0 < k) :
    levelPower W ρ S CD0 k (minPowerSpeed W ρ S CD0 k) <
      levelPower W ρ S CD0 k (minDragSpeed W ρ S CD0 k) := by
  exact levelPower_minPowerSpeed_lt hW hρ hS hCD0 hk
    (minDragSpeed_pos (ne_of_gt hW) hρ hS hCD0 hk)
    (ne_of_gt (minPowerSpeed_lt_minDragSpeed (ne_of_gt hW) hρ hS hCD0 hk))

/-- For positive weight and `ρ, S, CD0, k > 0`, the lift coefficient at the minimum-power speed is
`√(3 * CD0 / k)`, `√3` times the lift coefficient `√(CD0 / k)` at minimum drag; there the induced
drag `k * CL ^ 2` is three times the zero-lift drag `CD0`. -/
lemma levelLiftCoeff_minPowerSpeed {W ρ S CD0 k : ℝ} (hW : 0 < W) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) :
    levelLiftCoeff W ρ S (minPowerSpeed W ρ S CD0 k) = Real.sqrt (3 * CD0 / k) := by
  have hW0 : W ≠ 0 := ne_of_gt hW
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hCD00 : CD0 ≠ 0 := ne_of_gt hCD0
  have hm := minPowerSpeed_pos hW0 hρ hS hCD0 hk
  have hm4 := minPowerSpeed_pow_four hW0 hρ hS hCD0 hk
  unfold inducedDragFactor parasiteDragFactor at hm4
  have hCL_nonneg : 0 ≤ levelLiftCoeff W ρ S (minPowerSpeed W ρ S CD0 k) := by
    unfold levelLiftCoeff
    apply div_nonneg _ _
    · positivity
    · positivity
  have hsq : levelLiftCoeff W ρ S (minPowerSpeed W ρ S CD0 k) ^ 2 = 3 * CD0 / k := by
    have hm44 : (minPowerSpeed W ρ S CD0 k ^ 2) ^ 2
        = minPowerSpeed W ρ S CD0 k ^ 4 := by ring
    have hden : (ρ * minPowerSpeed W ρ S CD0 k ^ 2 * S) ^ 2
        = ρ ^ 2 * S ^ 2 * minPowerSpeed W ρ S CD0 k ^ 4 := by
      linear_combination (ρ ^ 2 * S ^ 2) * hm44
    unfold levelLiftCoeff
    rw [div_pow, hden, hm4]
    have hρ2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ0
    have hS2 : S ^ 2 ≠ 0 := pow_ne_zero 2 hS0
    have hρS : ρ * S ≠ 0 := mul_ne_zero hρ0 hS0
    have h3a' : 3 * (ρ * S * CD0 / 2) ≠ 0 := by positivity
    field_simp
  conv_lhs => rw [← Real.sqrt_sq hCL_nonneg]
  rw [hsq]

/-! ## K. Power on the stall-validity interval -/

/-- For `W > 0` and `ρ, S, CD0, k, CLmax > 0`, the minimum-power speed lies below the stall speed
exactly when its lift coefficient `√(3 * CD0 / k)` exceeds `CLmax`; it is then not an operating
point. -/
lemma minPowerSpeed_lt_stallSpeed_iff {W ρ S CD0 k CLmax : ℝ} (hW : 0 < W) (hρ : 0 < ρ)
    (hS : 0 < S) (hCD0 : 0 < CD0) (hk : 0 < k) (hCL : 0 < CLmax) :
    minPowerSpeed W ρ S CD0 k < stallSpeed W ρ S CLmax ↔ CLmax < Real.sqrt (3 * CD0 / k) := by
  have hW0 : W ≠ 0 := ne_of_gt hW
  have hmp := minPowerSpeed_pos hW0 hρ hS hCD0 hk
  have hiff := levelLiftCoeff_le_iff_stallSpeed_le hW hρ hS hCL hmp
  have hCL := levelLiftCoeff_minPowerSpeed hW hρ hS hCD0 hk
  rw [hCL] at hiff
  exact ⟨fun hlt => lt_of_not_ge (fun hge => not_le_of_gt hlt (hiff.mp hge)),
    fun hlt => lt_of_not_ge (fun hge => not_le_of_gt hlt (hiff.mpr hge))⟩

/-- Selection on the stall-validity interval: for `W > 0` and `ρ, S, CD0, k, CLmax > 0`, every
positive speed with lift coefficient at most `CLmax` other than `max V_s V_mp` needs strictly more
power than that speed. When `V_mp < V_s` the selected speed is the stall endpoint, not the
unconstrained minimizer. -/
lemma levelPower_max_lt {W ρ S CD0 k CLmax V : ℝ} (hW : 0 < W) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) (hCL : 0 < CLmax) (hV : 0 < V)
    (hadm : levelLiftCoeff W ρ S V ≤ CLmax)
    (hne : V ≠ max (stallSpeed W ρ S CLmax) (minPowerSpeed W ρ S CD0 k)) :
    levelPower W ρ S CD0 k (max (stallSpeed W ρ S CLmax) (minPowerSpeed W ρ S CD0 k)) <
      levelPower W ρ S CD0 k V := by
  have hsV : stallSpeed W ρ S CLmax ≤ V :=
    (levelLiftCoeff_le_iff_stallSpeed_le hW hρ hS hCL hV).mp hadm
  have hmono := levelPower_strictMonoOn hW hρ hS hCD0 hk
  rcases le_total (stallSpeed W ρ S CLmax) (minPowerSpeed W ρ S CD0 k) with hle | hle
  · rw [max_eq_right hle] at hne ⊢
    exact levelPower_minPowerSpeed_lt hW hρ hS hCD0 hk hV hne
  · rw [max_eq_left hle] at hne ⊢
    have hlt : stallSpeed W ρ S CLmax < V := lt_of_le_of_ne hsV (fun h => hne h.symm)
    exact hmono (show minPowerSpeed W ρ S CD0 k ≤ stallSpeed W ρ S CLmax from hle)
      (show minPowerSpeed W ρ S CD0 k ≤ V from le_trans hle hsV) hlt

/-- For `W > 0` and `ρ, S, CD0, k, CLmax > 0`, the least power required among positive speeds with
lift coefficient at most `CLmax` is attained at `max V_s V_mp`: at the minimum-power speed when it
is admissible and at the stall endpoint otherwise. -/
lemma isLeast_levelPower_stall {W ρ S CD0 k CLmax : ℝ} (hW : 0 < W) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hk : 0 < k) (hCL : 0 < CLmax) :
    IsLeast (levelPower W ρ S CD0 k '' {V | 0 < V ∧ levelLiftCoeff W ρ S V ≤ CLmax})
      (levelPower W ρ S CD0 k (max (stallSpeed W ρ S CLmax) (minPowerSpeed W ρ S CD0 k))) := by
  have hVs_pos : 0 < stallSpeed W ρ S CLmax := by
    unfold stallSpeed
    rw [Real.sqrt_pos]
    exact div_pos (mul_pos (by norm_num) hW) (mul_pos (mul_pos hρ hS) hCL)
  have hmax_pos : 0 < max (stallSpeed W ρ S CLmax) (minPowerSpeed W ρ S CD0 k) :=
    lt_of_lt_of_le hVs_pos (le_max_left _ _)
  have hVs_le : stallSpeed W ρ S CLmax
      ≤ max (stallSpeed W ρ S CLmax) (minPowerSpeed W ρ S CD0 k) :=
    le_max_left _ _
  have hadm : levelLiftCoeff W ρ S
      (max (stallSpeed W ρ S CLmax) (minPowerSpeed W ρ S CD0 k)) ≤ CLmax :=
    (levelLiftCoeff_le_iff_stallSpeed_le hW hρ hS hCL hmax_pos).mpr hVs_le
  constructor
  · exact ⟨max (stallSpeed W ρ S CLmax) (minPowerSpeed W ρ S CD0 k), ⟨hmax_pos, hadm⟩, rfl⟩
  · intro y hy
    obtain ⟨U, ⟨hU, hadmU⟩, rfl⟩ := hy
    by_cases heq : U = max (stallSpeed W ρ S CLmax) (minPowerSpeed W ρ S CD0 k)
    · rw [heq]
    · exact (levelPower_max_lt hW hρ hS hCD0 hk hCL hU hadmU heq).le

/-! ## L. Shaft power -/

/-- Shaft power `P(V) / η` that a propulsor of efficiency `η` must absorb to deliver the power
required `P(V)`; with the convention `x / 0 = 0` it is `0` at `η = 0`. The physical regime is
`0 < η ≤ 1`, with `η` a declared constant. -/
noncomputable def shaftPowerRequired (η W ρ S CD0 k V : ℝ) : ℝ :=
  levelPower W ρ S CD0 k V / η

/-- The efficiency is not silently one: when the power required is nonzero, the shaft power
equals it exactly when `η = 1`. -/
lemma shaftPowerRequired_eq_levelPower_iff {η W ρ S CD0 k V : ℝ}
    (hP : levelPower W ρ S CD0 k V ≠ 0) :
    shaftPowerRequired η W ρ S CD0 k V = levelPower W ρ S CD0 k V ↔ η = 1 := by
  unfold shaftPowerRequired
  constructor
  · intro h
    by_cases hη : η = 0
    · subst hη
      rw [div_zero] at h
      exact (hP h.symm).elim
    · have hmul := congrArg (fun x => x * η) h
      rw [div_mul_cancel₀ _ hη] at hmul
      have h2 : levelPower W ρ S CD0 k V * 1 = levelPower W ρ S CD0 k V * η := by
        rw [mul_one]
        exact hmul
      exact (mul_left_cancel₀ hP h2).symm
  · intro h
    subst h
    rw [div_one]

/-- For a constant efficiency `η > 0` and `ρ, S, CD0 > 0`, the shaft power has the same positive
minimizers as the power required, the speeds with `V ^ 4 = b / (3 * a)`. -/
lemma isMinOn_shaftPowerRequired_iff {η W ρ S CD0 k V : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (hS : 0 < S)
    (hCD0 : 0 < CD0) (hV : 0 < V) :
    IsMinOn (shaftPowerRequired η W ρ S CD0 k) (Set.Ioi 0) V ↔
      V ^ 4 = inducedDragFactor W ρ S k / (3 * parasiteDragFactor ρ S CD0) := by
  have hη0 : η ≠ 0 := ne_of_gt hη
  have hdiv : ∀ {x y : ℝ}, x / η ≤ y / η ↔ x ≤ y := fun {x y} => by
    rw [div_le_iff₀ hη, div_mul_cancel₀ _ hη0]
  rw [← isMinOn_levelPower_iff hρ hS hCD0 hV]
  unfold shaftPowerRequired
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro h U hU
    exact hdiv.mp (h U hU)
  · intro h U hU
    exact hdiv.mpr (h U hU)

/-! ## M. Thrust-specific fuel law in quasi-level cruise -/

/-- Lift-to-drag ratio `Λ = CL / (CD0 + k * CL ^ 2)` of the declared polar at the lift coefficient
`CL`; it does not depend on density, speed or weight. With the convention `x / 0 = 0`, `Λ = 0` when
`CD0 + k * CL ^ 2 = 0`. -/
noncomputable def polarLiftToDrag (CD0 k CL : ℝ) : ℝ :=
  CL / (CD0 + k * CL ^ 2)

/-- Quasi-level cruise at a fixed lift coefficient: if the lift `ρ * V ^ 2 / 2 * S * CL` equals the
weight `W` and `CL ≠ 0`, the polar drag is `W / Λ` (both sides are `0` when `CD0 + k * CL ^ 2 = 0`).
With thrust along the velocity balancing that drag, the weight-based fuel law `W' = -cW * T` becomes
`W' = -cW * W / Λ`. -/
lemma polarDrag_eq_div_polarLiftToDrag {W ρ S CD0 k CL V : ℝ} (hCL : CL ≠ 0)
    (hL : ρ * V ^ 2 / 2 * S * CL = W) :
    polarDrag ρ S CD0 k CL V = W / polarLiftToDrag CD0 k CL := by
  unfold polarDrag polarLiftToDrag
  by_cases hD : CD0 + k * CL ^ 2 = 0
  · simp [hD]
  · have h : W / (CL / (CD0 + k * CL ^ 2)) = W * (CD0 + k * CL ^ 2) / CL := by
      field_simp
    rw [h, ← hL]
    field_simp

/-! ## N. The weight history -/

/-- Weight `W(t) = Wi * exp (-(cW / Λ) * t)` at time `t` of the cruise that starts at the weight
`Wi`, with weight-based fuel coefficient `cW` (an inverse time) and lift-to-drag ratio `Λ`; with the
convention `x / 0 = 0` it is the constant `Wi` when `Λ = 0`. In the physical reading
`Wi, cW, Λ > 0`. -/
noncomputable def cruiseWeight (Wi cW Λ t : ℝ) : ℝ :=
  Wi * Real.exp (-(cW / Λ) * t)

/-- The cruise weight solves the thrust-specific fuel law: it starts at `Wi` and
`W' = -cW * W / Λ` at every time. -/
lemma cruiseWeight_solves (Wi cW Λ : ℝ) :
    cruiseWeight Wi cW Λ 0 = Wi ∧
      ∀ t, HasDerivAt (cruiseWeight Wi cW Λ) (-cW * cruiseWeight Wi cW Λ t / Λ) t := by
  have h := MetaMathlibExt.scalar_exp_solution (x := cruiseWeight Wi cW Λ)
    (a := (-(cW / Λ))) (x₀ := Wi) (fun t => rfl)
  refine ⟨h.1, fun t => (h.2 t).congr_deriv ?_⟩
  ring

/-- Integrating factor: along a solution of `W' = -cW * W / Λ` the product
`W(t) * exp ((cW / Λ) * t)` has derivative `0`. -/
lemma hasDerivAt_mul_exp_eq_zero {W : ℝ → ℝ} {cW Λ t : ℝ}
    (hW : HasDerivAt W (-cW * W t / Λ) t) :
    HasDerivAt (fun s => W s * Real.exp (cW / Λ * s)) 0 t := by
  have hexp : HasDerivAt (fun s => Real.exp (cW / Λ * s))
      ((cW / Λ) * Real.exp (cW / Λ * t)) t :=
    (((hasDerivAt_id' t).const_mul (cW / Λ)).exp.congr_deriv (by ring))
  have hmul := hW.mul hexp
  apply hmul.congr_deriv
  ring

/-- Uniqueness: a solution of `W' = -cW * W / Λ` on `[0, t₁]` is the cruise weight from its
initial value `W 0`. -/
lemma eq_cruiseWeight_of_hasDerivAt {W : ℝ → ℝ} {cW Λ t₁ : ℝ}
    (hW : ∀ t ∈ Set.Icc 0 t₁, HasDerivAt W (-cW * W t / Λ) t) :
    ∀ t ∈ Set.Icc 0 t₁, W t = cruiseWeight (W 0) cW Λ t := by
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have htt₁ : t ≤ t₁ := ht.2
  have hsub : Set.Icc 0 t ⊆ Set.Icc 0 t₁ :=
    Set.Icc_subset_Icc_right htt₁
  have hF : ∀ s ∈ Set.uIcc 0 t,
      HasDerivAt (fun s => W s * Real.exp (cW / Λ * s)) 0 s := by
    rw [Set.uIcc_of_le ht0]
    intro s hs
    exact hasDerivAt_mul_exp_eq_zero (hW s (hsub hs))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (intervalIntegrable_const (c := (0 : ℝ)))
  simp only [intervalIntegral.integral_const, sub_zero, smul_zero] at hFTC
  have hFeq : W t * Real.exp (cW / Λ * t) = W 0 := by
    simp at hFTC
    linarith
  have hexp_ne : Real.exp (cW / Λ * t) ≠ 0 := Real.exp_ne_zero _
  have hW_eq : W t = W 0 * Real.exp (-(cW / Λ) * t) := by
    have h1 : W t = (W t * Real.exp (cW / Λ * t)) / Real.exp (cW / Λ * t) := by
      field_simp
    rw [hFeq] at h1
    have h2 : (W 0 : ℝ) / Real.exp (cW / Λ * t)
        = W 0 * Real.exp (-(cW / Λ) * t) := by
      have harg : (-(cW / Λ) * t : ℝ) = -(cW / Λ * t) := by ring
      rw [harg, Real.exp_neg]
      ring
    rw [h1, h2]
  rw [hW_eq]
  rfl

/-! ## O. Duration and range -/

/-- Breguet endurance `Λ / cW * log (Wi / Wf)`: the cruise time from the weight `Wi` down to `Wf`.
With the conventions `x / 0 = 0`, `log 0 = 0` and `log x = log |x|` it is `0` when `cW = 0`,
`Wi = 0` or `Wf = 0`, and `Λ / cW * log |Wi / Wf|` when `Wi / Wf < 0`. -/
noncomputable def breguetDuration (Λ cW Wi Wf : ℝ) : ℝ :=
  Λ / cW * Real.log (Wi / Wf)

/-- Time to the final weight: for `Wi, Wf > 0` and `cW, Λ > 0`, the cruise weight equals `Wf`
exactly at the Breguet duration. -/
lemma cruiseWeight_eq_iff {Wi Wf cW Λ t : ℝ} (hWi : 0 < Wi) (hWf : 0 < Wf) (hcW : 0 < cW)
    (hΛ : 0 < Λ) :
    cruiseWeight Wi cW Λ t = Wf ↔ t = breguetDuration Λ cW Wi Wf := by
  have hWi_ne : Wi ≠ 0 := ne_of_gt hWi
  have hWf_ne : Wf ≠ 0 := ne_of_gt hWf
  have hcW_ne : cW ≠ 0 := ne_of_gt hcW
  have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ
  have hk_ne : cW / Λ ≠ 0 := div_ne_zero hcW_ne hΛ_ne
  have hRatio_pos : 0 < Wf / Wi := div_pos hWf hWi
  have hexp_log : Real.exp (Real.log (Wf / Wi)) = Wf / Wi := Real.exp_log hRatio_pos
  have hlog_neg : Real.log (Wf / Wi) = -Real.log (Wi / Wf) := by
    rw [Real.log_div hWf_ne hWi_ne, Real.log_div hWi_ne hWf_ne]
    ring
  unfold cruiseWeight breguetDuration
  have h1 : Wi * Real.exp (-(cW / Λ) * t) = Wf
      ↔ Real.exp (-(cW / Λ) * t) = Wf / Wi := by
    rw [eq_div_iff hWi_ne, mul_comm]
  rw [h1, ← hexp_log, Real.exp_injective.eq_iff, hlog_neg]
  constructor
  · intro h
    have hkt : (cW / Λ) * t = Real.log (Wi / Wf) := by linear_combination -h
    have htdiv : t = Real.log (Wi / Wf) / (cW / Λ) := by
      rw [eq_div_iff hk_ne, mul_comm]
      exact hkt
    have hfield : Real.log (Wi / Wf) / (cW / Λ) = Λ / cW * Real.log (Wi / Wf) := by
      field_simp
    rw [htdiv, hfield]
  · intro h
    rw [h]
    field_simp

/-- Duration: for `cW, Λ > 0` and `t₁ ≥ 0`, a cruise that obeys `W' = -cW * W / Λ` on `[0, t₁]`
with positive initial weight lasts `t₁ = Λ / cW * log (W 0 / W t₁)`, the time to burn from
`Wi = W 0` down to `Wf = W t₁`. -/
lemma cruise_duration_eq {W : ℝ → ℝ} {cW Λ t₁ : ℝ} (hcW : 0 < cW) (hΛ : 0 < Λ) (ht₁ : 0 ≤ t₁)
    (hW : ∀ t ∈ Set.Icc 0 t₁, HasDerivAt W (-cW * W t / Λ) t) (hW0 : 0 < W 0) :
    t₁ = breguetDuration Λ cW (W 0) (W t₁) := by
  have hmem : t₁ ∈ Set.Icc 0 t₁ := ⟨ht₁, le_rfl⟩
  have hW_eq := eq_cruiseWeight_of_hasDerivAt hW t₁ hmem
  have hW1_pos : 0 < W t₁ := by
    rw [hW_eq]
    unfold cruiseWeight
    exact mul_pos hW0 (Real.exp_pos _)
  exact (cruiseWeight_eq_iff hW0 hW1_pos hcW hΛ).mp hW_eq.symm

/-- Range: for `cW, Λ > 0`, `t₁ ≥ 0` and a cruise that obeys `W' = -cW * W / Λ` on `[0, t₁]` with
positive initial weight, flying at the constant air speed `V` (`s' = V` on `[0, t₁]`) covers the
air-path distance `s t₁ - s 0 = V * (Λ / cW * log (W 0 / W t₁))`, the speed times the duration. -/
lemma cruise_range_eq {W s : ℝ → ℝ} {V cW Λ t₁ : ℝ} (hcW : 0 < cW) (hΛ : 0 < Λ) (ht₁ : 0 ≤ t₁)
    (hW : ∀ t ∈ Set.Icc 0 t₁, HasDerivAt W (-cW * W t / Λ) t) (hW0 : 0 < W 0)
    (hs : ∀ t ∈ Set.Icc 0 t₁, HasDerivAt s V t) :
    s t₁ - s 0 = V * breguetDuration Λ cW (W 0) (W t₁) := by
  have hs' : ∀ x ∈ Set.uIcc 0 t₁, HasDerivAt s V x := by
    rw [Set.uIcc_of_le ht₁]
    exact hs
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := s) (f' := fun _ => V)
    hs' (intervalIntegrable_const (c := V))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hFTC
  have hdur := cruise_duration_eq hcW hΛ ht₁ hW hW0
  have hcongr : t₁ * V = breguetDuration Λ cW (W 0) (W t₁) * V := congrArg (· * V) hdur
  have htV : t₁ * V = V * breguetDuration Λ cW (W 0) (W t₁) :=
    hcongr.trans (mul_comm _ _)
  exact hFTC.symm.trans htV

/-- A burn from `Wi` down to a smaller positive `Wf` takes positive time when `cW, Λ > 0`; at a
positive speed it covers a positive range. -/
lemma breguetDuration_pos {Λ cW Wi Wf : ℝ} (hΛ : 0 < Λ) (hcW : 0 < cW) (hWf : 0 < Wf)
    (hlt : Wf < Wi) : 0 < breguetDuration Λ cW Wi Wf := by
  have hdiv : 1 < Wi / Wf := (one_lt_div hWf).mpr hlt
  have hlog : 0 < Real.log (Wi / Wf) := Real.log_pos hdiv
  have hfrac : 0 < Λ / cW := div_pos hΛ hcW
  unfold breguetDuration
  exact mul_pos hfrac hlog

/-- No burn, no time: `Wi = Wf` gives zero duration. -/
lemma breguetDuration_self (Λ cW W : ℝ) : breguetDuration Λ cW W W = 0 := by
  unfold breguetDuration
  by_cases hW : W = 0
  · simp [hW]
  · rw [div_self hW, Real.log_one, mul_zero]

/-! ## P. Mass-based fuel coefficient -/

/-- Conversion to the weight-based coefficient: if the mass burns at `m' = -cm * T` for the thrust
`T` and the weight is `W = g * m`, then `W' = -(g * cm) * T`, so `cW = g * cm`. -/
lemma hasDerivAt_weight_of_mass {m : ℝ → ℝ} {cm g T t : ℝ} (hm : HasDerivAt m (-cm * T) t) :
    HasDerivAt (fun s => g * m s) (-(g * cm) * T) t := by
  exact (hm.const_mul g).congr_deriv (by ring)

/-- Mass form of the duration: if the mass obeys `m' = -cm * (g * m / Λ)` on `[0, t₁]` (thrust
`W / Λ` for the weight `W = g * m`) with `cm, g, Λ > 0`, `t₁ ≥ 0` and `m 0 > 0`, the cruise lasts
`t₁ = Λ / (g * cm) * log (m 0 / m t₁)`. -/
lemma cruise_duration_mass_eq {m : ℝ → ℝ} {cm g Λ t₁ : ℝ} (hcm : 0 < cm) (hg : 0 < g)
    (hΛ : 0 < Λ) (ht₁ : 0 ≤ t₁)
    (hm : ∀ t ∈ Set.Icc 0 t₁, HasDerivAt m (-cm * (g * m t / Λ)) t) (hm0 : 0 < m 0) :
    t₁ = breguetDuration Λ (g * cm) (m 0) (m t₁) := by
  have hcW : 0 < g * cm := mul_pos hg hcm
  have hm' : ∀ t ∈ Set.Icc 0 t₁, HasDerivAt m (-(g * cm) * m t / Λ) t :=
    fun t ht => (hm t ht).congr_deriv (by ring)
  exact cruise_duration_eq hcW hΛ ht₁ hm' hm0

/-- Confusing the coefficients loses a factor `g`: for `g ≠ 0`, using the mass-based `cm` where the
weight-based `g * cm` belongs multiplies the duration, and so the range, by `g`. -/
lemma breguetDuration_mass_confusion {Λ cm g Wi Wf : ℝ} (hg : g ≠ 0) :
    breguetDuration Λ cm Wi Wf = g * breguetDuration Λ (g * cm) Wi Wf := by
  unfold breguetDuration
  by_cases hcm : cm = 0
  · simp [hcm]
  · have hgcm : g * cm ≠ 0 := mul_ne_zero hg hcm
    field_simp

/-! ## Q. The cruise schedule -/

/-- No fixed-altitude cruise: with fixed density, speed and lift coefficient the lift is fixed, so
if it balances the initial weight `Wi > 0` it balances the cruise weight at no later time `t > 0`
of a burn with `cW, Λ > 0`. -/
lemma lift_ne_cruiseWeight_of_fixed_density {ρ V S CL Wi cW Λ t : ℝ} (hWi : 0 < Wi)
    (hcW : 0 < cW) (hΛ : 0 < Λ) (ht : 0 < t) (h0 : ρ * V ^ 2 / 2 * S * CL = Wi) :
    ρ * V ^ 2 / 2 * S * CL ≠ cruiseWeight Wi cW Λ t := by
  rw [h0]
  unfold cruiseWeight
  have hk : 0 < cW / Λ := div_pos hcW hΛ
  have hneg : -(cW / Λ) < 0 := neg_lt_zero.mpr hk
  have harg : (-(cW / Λ)) * t < 0 := mul_neg_of_neg_of_pos hneg ht
  have hexp : Real.exp (-(cW / Λ) * t) < 1 := Real.exp_lt_one_iff.mpr harg
  have hlt : Wi * Real.exp (-(cW / Λ) * t) < Wi := by
    have h := mul_lt_mul_of_pos_left hexp hWi
    rwa [mul_one] at h
  exact ne_of_gt hlt

/-- Isothermal cruise-climb: in an isothermal layer with `g, Rs, T > 0`, if the lift at the height
`z₀` balances the initial weight `Wi`, then at the same speed and lift coefficient the lift at the
height `z₀ + H * (cW / Λ) * t`, with `H` the scale height, balances the cruise weight at time
`t`. -/
lemma lift_cruiseClimb {ρ0 g Rs T V S CL Wi cW Λ z₀ : ℝ} (hg : 0 < g) (hRs : 0 < Rs)
    (hT : 0 < T) (h0 : isothermalDensity ρ0 g Rs T z₀ * V ^ 2 / 2 * S * CL = Wi) (t : ℝ) :
    isothermalDensity ρ0 g Rs T (z₀ + scaleHeight Rs T g * (cW / Λ) * t) * V ^ 2 / 2 * S * CL =
      cruiseWeight Wi cW Λ t := by
  have hH_pos : 0 < scaleHeight Rs T g := by
    unfold scaleHeight
    rw [abs_of_pos hg]
    exact div_pos (mul_pos hRs hT) hg
  have hH_ne : scaleHeight Rs T g ≠ 0 := ne_of_gt hH_pos
  have h0_exp := isothermalDensity_eq_exp hg hRs hT ρ0 z₀
  have hz_exp := isothermalDensity_eq_exp hg hRs hT ρ0
    (z₀ + scaleHeight Rs T g * (cW / Λ) * t)
  rw [h0_exp] at h0
  rw [hz_exp]
  unfold cruiseWeight
  have hexp_arg : (-(z₀ + scaleHeight Rs T g * (cW / Λ) * t) / scaleHeight Rs T g)
      = (-z₀ / scaleHeight Rs T g) + (-(cW / Λ) * t) := by
    field_simp
    ring
  rw [hexp_arg, Real.exp_add]
  have hring : ρ0 * (Real.exp (-z₀ / scaleHeight Rs T g)
      * Real.exp (-(cW / Λ) * t)) * V ^ 2 / 2 * S * CL
      = (ρ0 * Real.exp (-z₀ / scaleHeight Rs T g) * V ^ 2 / 2 * S * CL)
        * Real.exp (-(cW / Λ) * t) := by ring
  rw [hring, h0]

/-- The cruise-climb is forced: with `ρ0, g, Rs, T > 0` and nonzero `V, S, CL`, if the lift at the
height `z₀` balances the initial weight `Wi`, a height at which the lift balances the cruise weight
at time `t` is `z₀ + H * (cW / Λ) * t`. -/
lemma eq_cruiseClimb_of_lift_eq {ρ0 g Rs T V S CL Wi cW Λ z₀ z t : ℝ} (hρ0 : 0 < ρ0)
    (hg : 0 < g) (hRs : 0 < Rs) (hT : 0 < T) (hV : V ≠ 0) (hS : S ≠ 0) (hCL : CL ≠ 0)
    (h0 : isothermalDensity ρ0 g Rs T z₀ * V ^ 2 / 2 * S * CL = Wi)
    (hz : isothermalDensity ρ0 g Rs T z * V ^ 2 / 2 * S * CL = cruiseWeight Wi cW Λ t) :
    z = z₀ + scaleHeight Rs T g * (cW / Λ) * t := by
  have hH_pos : 0 < scaleHeight Rs T g := by
    unfold scaleHeight
    rw [abs_of_pos hg]
    exact div_pos (mul_pos hRs hT) hg
  have hH_ne : scaleHeight Rs T g ≠ 0 := ne_of_gt hH_pos
  have hClimb := lift_cruiseClimb (cW := cW) (Λ := Λ) hg hRs hT h0 t
  have heq : isothermalDensity ρ0 g Rs T z * V ^ 2 / 2 * S * CL
      = isothermalDensity ρ0 g Rs T (z₀ + scaleHeight Rs T g * (cW / Λ) * t)
        * V ^ 2 / 2 * S * CL := hz.trans hClimb.symm
  have hV2 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV
  have hV2d : V ^ 2 / 2 ≠ 0 := div_ne_zero hV2 (by norm_num)
  have hC : V ^ 2 / 2 * S * CL ≠ 0 := mul_ne_zero (mul_ne_zero hV2d hS) hCL
  have hfactor : ∀ d : ℝ, d * V ^ 2 / 2 * S * CL = d * (V ^ 2 / 2 * S * CL) := fun d => by ring
  rw [hfactor, hfactor] at heq
  have hdens : isothermalDensity ρ0 g Rs T z
      = isothermalDensity ρ0 g Rs T (z₀ + scaleHeight Rs T g * (cW / Λ) * t) :=
    mul_right_cancel₀ hC heq
  have hz_exp := isothermalDensity_eq_exp hg hRs hT ρ0 z
  have hzc_exp := isothermalDensity_eq_exp hg hRs hT ρ0
    (z₀ + scaleHeight Rs T g * (cW / Λ) * t)
  rw [hz_exp, hzc_exp] at hdens
  have hexp_eq : Real.exp (-z / scaleHeight Rs T g)
      = Real.exp (-(z₀ + scaleHeight Rs T g * (cW / Λ) * t) / scaleHeight Rs T g) :=
    mul_left_cancel₀ (ne_of_gt hρ0) hdens
  have harg_eq : -z / scaleHeight Rs T g
      = -(z₀ + scaleHeight Rs T g * (cW / Λ) * t) / scaleHeight Rs T g :=
    Real.exp_injective hexp_eq
  have hmul := congrArg (· * scaleHeight Rs T g) harg_eq
  simp only [div_mul_cancel₀ _ hH_ne] at hmul
  linarith

/-- Altitude-band check of the isothermal cruise-climb: for `Rs, T > 0`, `cW, Λ > 0` and
`Wi ≥ Wf > 0`, the height `z₀ + H * (cW / Λ) * t` stays in the declared band `[z₁, z₂]` during the
whole cruise `0 ≤ t ≤ Λ / cW * log (Wi / Wf)` exactly when `z₁ ≤ z₀` and
`z₀ + H * log (Wi / Wf) ≤ z₂`: the cruise climbs `H * log (Wi / Wf)`. -/
lemma cruiseClimb_mem_band_iff {Rs T g cW Λ Wi Wf z₀ z₁ z₂ : ℝ} (hRs : 0 < Rs) (hT : 0 < T)
    (hcW : 0 < cW) (hΛ : 0 < Λ) (hWf : 0 < Wf) (hle : Wf ≤ Wi) :
    (∀ t ∈ Set.Icc 0 (breguetDuration Λ cW Wi Wf),
        z₀ + scaleHeight Rs T g * (cW / Λ) * t ∈ Set.Icc z₁ z₂) ↔
      z₁ ≤ z₀ ∧ z₀ + scaleHeight Rs T g * Real.log (Wi / Wf) ≤ z₂ := by
  have hH_nonneg : 0 ≤ scaleHeight Rs T g := by
    unfold scaleHeight
    exact div_nonneg (le_of_lt (mul_pos hRs hT)) (abs_nonneg _)
  have hk_nonneg : 0 ≤ scaleHeight Rs T g * (cW / Λ) :=
    mul_nonneg hH_nonneg (le_of_lt (div_pos hcW hΛ))
  have h1le : 1 ≤ Wi / Wf := (one_le_div hWf).mpr hle
  have hlog_nonneg : 0 ≤ Real.log (Wi / Wf) := Real.log_nonneg h1le
  have hD_nonneg : 0 ≤ breguetDuration Λ cW Wi Wf := by
    unfold breguetDuration
    exact mul_nonneg (le_of_lt (div_pos hΛ hcW)) hlog_nonneg
  have hcW_ne : cW ≠ 0 := ne_of_gt hcW
  have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ
  have hfD : z₀ + scaleHeight Rs T g * (cW / Λ) * breguetDuration Λ cW Wi Wf
      = z₀ + scaleHeight Rs T g * Real.log (Wi / Wf) := by
    have hcancel : (cW / Λ) * (Λ / cW) = (1 : ℝ) := by field_simp
    unfold breguetDuration
    have hring : scaleHeight Rs T g * (cW / Λ) * (Λ / cW * Real.log (Wi / Wf))
        = scaleHeight Rs T g * ((cW / Λ) * (Λ / cW)) * Real.log (Wi / Wf) := by ring
    rw [hring, hcancel]
    ring
  have hf0 : z₀ + scaleHeight Rs T g * (cW / Λ) * 0 = z₀ := by simp
  constructor
  · intro h
    have h0_mem : (0 : ℝ) ∈ Set.Icc 0 (breguetDuration Λ cW Wi Wf) :=
      ⟨le_rfl, hD_nonneg⟩
    have hD_mem : breguetDuration Λ cW Wi Wf ∈ Set.Icc 0 (breguetDuration Λ cW Wi Wf) :=
      ⟨hD_nonneg, le_rfl⟩
    have h0' := h 0 h0_mem
    have hD' := h _ hD_mem
    rw [Set.mem_Icc] at h0' hD'
    rw [hf0] at h0'
    rw [hfD] at hD'
    exact ⟨h0'.1, hD'.2⟩
  · intro h t ht
    have ht' := Set.mem_Icc.mp ht
    have hle1 : z₀ ≤ z₀ + scaleHeight Rs T g * (cW / Λ) * t := by
      have hkt : 0 ≤ scaleHeight Rs T g * (cW / Λ) * t :=
        mul_nonneg hk_nonneg ht'.1
      linarith
    have hle2 : z₀ + scaleHeight Rs T g * (cW / Λ) * t
        ≤ z₀ + scaleHeight Rs T g * (cW / Λ) * breguetDuration Λ cW Wi Wf := by
      have hkt : scaleHeight Rs T g * (cW / Λ) * t
          ≤ scaleHeight Rs T g * (cW / Λ) * breguetDuration Λ cW Wi Wf :=
        mul_le_mul_of_nonneg_left ht'.2 hk_nonneg
      linarith
    rw [hfD] at hle2
    exact Set.mem_Icc.mpr ⟨le_trans h.1 hle1, le_trans hle2 h.2⟩

end AircraftPerformance
