/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import PhyslibExt.EarthScience.IsothermalAtmosphericPressure

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Aircraft performance: isothermal density and the level-flight drag polar

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
because the drag depends on `W` only through `W ^ 2`. If `CD0 = 0`, `k = 0` or `W = 0`, one drag
term vanishes, `D(V)` has no minimum over positive speeds, and `minDragSpeed` takes the
meaningless value `0`. The polar is valid only up to a declared maximum lift coefficient
`CLmax`; at a positive speed this is the stall-validity interval
`V ≥ V_s = √(2 * W / (ρ * S * CLmax))`, whose radicand is positive only for `W > 0`.
The algebraic minimizer is an operating point only when it lies in that interval:
`exists_levelDrag_eq_two_sqrt_iff` and `two_sqrt_lt_levelDrag_of_minDragSpeed_lt_stallSpeed`. At
`V = 0` Lean's convention `x / 0 = 0` gives meaningless values; no statement uses them.

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

## iii. Table of contents

- A. Scale height and density
- B. Bounds on a declared band
- C. Change of units
- D. Level flight on the declared polar
- E. Minimum drag
- F. The stall-validity interval
- G. Isothermal-layer density as the density input

## iv. References

- J. D. Anderson, *Introduction to Flight*, McGraw-Hill, ch. 3 (the standard atmosphere and
  its isothermal layers, `ρ / ρ₁ = exp (-(g₀ / (R T)) (h - h₁))`) and ch. 6 (drag polar
  `CD = CD0 + K * CL ^ 2`, thrust required in level flight, minimum thrust required where
  zero-lift drag equals drag due to lift, and for positive weight
  `(L / D)max = 1 / (2 * √(K * CD0))`).
- D. P. Raymer, *Aircraft Design: A Conceptual Approach*, AIAA, ch. 17 (level-flight
  performance and stall speed `V_s = √(2 * W / (ρ * S * CLmax))`).
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
relation `ρ = p / (Rs * T)` applied to `isothermalPressure` with reference pressure
`ρ0 * Rs * T`. The physical regime is `ρ0, g, Rs, T > 0`, `z` upward, `z` in a declared band. -/
noncomputable def isothermalDensity (ρ0 g Rs T z : ℝ) : ℝ :=
  isothermalPressure (ρ0 * Rs * T) g Rs T z / (Rs * T)

/-- The density obtained from the pressure profile and the ideal-gas relation is
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

/-- Hydrostatic balance in density form: the pressure profile with reference pressure
`ρ0 * Rs * T` satisfies `p'(z) = -ρ(z) * g` for `ρ = isothermalDensity ρ0 g Rs T`. -/
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

/-- On a declared band `[z₁, z₂]` the density strictly decreases with height. -/
lemma isothermalDensity_strictAntiOn {ρ0 g Rs T : ℝ} (hρ0 : 0 < ρ0) (hg : 0 < g)
    (hRs : 0 < Rs) (hT : 0 < T) (z₁ z₂ : ℝ) :
    StrictAntiOn (isothermalDensity ρ0 g Rs T) (Set.Icc z₁ z₂) := by
  have hRT : (0:ℝ) < Rs * T := mul_pos hRs hT
  have hpress := isothermalPressure_strictAnti (mul_pos (mul_pos hρ0 hRs) hT) hg hRs hT
  intro a _ b _ hab
  unfold isothermalDensity
  exact (div_lt_div_iff_of_pos_right hRT).mpr (hpress hab)

/-- Engineering density bounds on a declared band: for `z ∈ [z₁, z₂]`,
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

/-- The band bounds do not extend beyond the band: below `z₁` the density exceeds the upper
bound `ρ0 * exp (-z₁ / H)`, and above `z₂` it falls below the lower bound
`ρ0 * exp (-z₂ / H)`. The band hypothesis of `isothermalDensity_band_bounds` cannot be
dropped. -/
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

/-- The density formula commutes with a change of units with length, time and temperature
factors `l, s, k > 0`, for every mass factor `m`: rescaled inputs give the rescaled density. -/
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

/-- The scale height transforms as a length under a change of units. -/
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

/-- Lift coefficient required for level flight `L = W` at speed `V`:
`CL = 2 * W / (ρ * V ^ 2 * S)`. -/
noncomputable def levelLiftCoeff (W ρ S V : ℝ) : ℝ :=
  2 * W / (ρ * V ^ 2 * S)

/-- Parasite-drag factor `a = ρ * S * CD0 / 2`: the zero-lift drag at speed `V` is `a * V ^ 2`. -/
noncomputable def parasiteDragFactor (ρ S CD0 : ℝ) : ℝ :=
  ρ * S * CD0 / 2

/-- Induced-drag factor `b = 2 * k * W ^ 2 / (ρ * S)`: the drag due to lift in level flight at
speed `V` is `b / V ^ 2`. -/
noncomputable def inducedDragFactor (W ρ S k : ℝ) : ℝ :=
  2 * k * W ^ 2 / (ρ * S)

/-- Level-flight drag `D(V) = a * V ^ 2 + b / V ^ 2` of the declared polar. -/
noncomputable def levelDrag (W ρ S CD0 k V : ℝ) : ℝ :=
  parasiteDragFactor ρ S CD0 * V ^ 2 + inducedDragFactor W ρ S k / V ^ 2

/-- At the level-flight lift coefficient the lift `ρ * V ^ 2 / 2 * S * CL` equals the weight. -/
lemma lift_levelLiftCoeff {ρ S V : ℝ} (hρ : ρ ≠ 0) (hS : S ≠ 0) (hV : V ≠ 0) (W : ℝ) :
    ρ * V ^ 2 / 2 * S * levelLiftCoeff W ρ S V = W := by
  have hV2 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV
  have hden : ρ * V ^ 2 * S ≠ 0 := mul_ne_zero (mul_ne_zero hρ hV2) hS
  unfold levelLiftCoeff
  field_simp

/-- Imposing level flight with thrust along the velocity: if the lift
`ρ * V ^ 2 / 2 * S * CL` equals the weight `W`, the polar drag is
`D(V) = a * V ^ 2 + b / V ^ 2`. -/
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
unique positive speed of least level-flight drag
(`levelDrag_eq_two_sqrt_iff_eq_minDragSpeed`). As a formula it is the positive root of
`V ^ 4 = b / a` whenever `W ≠ 0` and `ρ, S, CD0, k > 0` (`minDragSpeed_pos`,
`minDragSpeed_pow_four`). If `CD0 = 0`, `k = 0` or `W = 0`, Lean's conventions `x / 0 = 0` and
`√0 = 0` give the meaningless value `0`. -/
noncomputable def minDragSpeed (W ρ S CD0 k : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (inducedDragFactor W ρ S k / parasiteDragFactor ρ S CD0))

/-- Arithmetic-geometric mean bound: at every nonzero speed `2 * √(a * b) ≤ D(V)`. -/
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

/-- Equality in the bound holds exactly when `V ^ 4 = b / a`. -/
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

/-- Engineering form of the bound, an identity for all parameters:
`2 * √(a * b) = 2 * |W| * √(CD0 * k)`. For positive weight and `ρ, S, CD0, k > 0` it is the
minimum drag (`isLeast_levelDrag`); in level flight the lift equals the weight `W`, so the
greatest lift-to-drag ratio is `W / (2 * W * √(CD0 * k)) = 1 / (2 * √(CD0 * k))`. That
consequence needs `W > 0`: for `W < 0` the lift is negative and the ratio at minimum drag is
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
`CLmax`. The physical regime is `W, ρ, S, CLmax > 0`; for `W ≤ 0` the radicand is not positive
and `Real.sqrt` returns the meaningless value `0`, so the stall results assume `0 < W`. -/
noncomputable def stallSpeed (W ρ S CLmax : ℝ) : ℝ :=
  Real.sqrt (2 * W / (ρ * S * CLmax))

/-- The stall-validity interval: for positive weight, at a positive speed the level-flight lift
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

/-- Subject to the stall-validity interval: for positive weight, some positive speed with lift
coefficient at most `CLmax` attains the bound `2 * √(a * b)` exactly when the stall speed is at
most the minimum-drag speed. -/
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

/-- An unconstrained minimizer below the stall speed is not an operating point: for positive
weight and `CD0, k > 0`, every positive speed with lift coefficient at most `CLmax` has drag
strictly above `2 * √(a * b)`. -/
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

/-- The stall speed exceeds the minimum-drag speed exactly when the lift coefficient at minimum
drag, `√(CD0 / k)`, exceeds `CLmax`. -/
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

/-- The density of the isothermal layer at any height `z` is an admissible density input: the
level-flight drag at every nonzero speed is at least `2 * √(a * b)` evaluated at that density. -/
lemma two_sqrt_le_levelDrag_isothermalDensity {ρ0 Rs T S CD0 k V : ℝ} (hρ0 : 0 < ρ0)
    (hRs : 0 < Rs) (hT : 0 < T) (hS : 0 < S) (hCD0 : 0 ≤ CD0) (hk : 0 ≤ k) (hV : V ≠ 0)
    (W g z : ℝ) :
    2 * Real.sqrt (parasiteDragFactor (isothermalDensity ρ0 g Rs T z) S CD0 *
        inducedDragFactor W (isothermalDensity ρ0 g Rs T z) S k) ≤
      levelDrag W (isothermalDensity ρ0 g Rs T z) S CD0 k V := by
  exact two_sqrt_le_levelDrag (isothermalDensity_pos hρ0 hRs hT g z) hS hCD0 hk hV

end AircraftPerformance
