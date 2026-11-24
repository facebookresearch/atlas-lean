/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PhyslibExt.EarthScience.ConductiveGeotherm

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Energy source removal: steady slab, heated cylinder and coolant channel

## i. Overview

A steady one-dimensional slab of thickness `L` and constant conductivity
`k` with uniform volumetric heat source `H` (an externally supplied
source term, per unit area fluxes). The temperature profile is the
existing geotherm profile of `PhyslibExt.EarthScience.ConductiveGeotherm`
read as a slab; this file names the slab quantities, proves the total
outward heat removal `H * L`, and identifies the midplane maximum for
equal surface temperatures. Section C adds the regular heated-cylinder
profile with the same constant-conductivity, uniform-source model, its
radial heat-balance equation, and its outward boundary power. No transient behavior is claimed: with the
source cut off (`H = 0`) the steady profile is the constant or linear
steady branch, not an instantaneous prediction.

Section D treats a steady single-phase coolant with constant specific heat `cp` flowing at mass flow
`ṁ > 0` along a heated channel `[-L/2, L/2]` of length `L > 0`. The linear power is the prescribed
chopped cosine `q'(z) = q₀ cos (π z / Lₑ)` with peak `q₀ ≥ 0` and extrapolated length `Lₑ ≥ L`, so
it lies between `0` and `q₀` on the heated length. The energy balance of a channel slice is the
two-port balance with no shaft work and no storage, enthalpy `h = cp T` and kinetic and potential
changes neglected: `ṁ cp T' = q'`. Integrating it from the inlet `T(-L/2) = T_in` gives
`T(z) = T_in + q₀ Lₑ (sin (π z / Lₑ) + sin (π L / (2 Lₑ))) / (π ṁ cp)`, the outlet
`T_out = T_in + 2 q₀ Lₑ sin (π L / (2 Lₑ)) / (π ṁ cp)`, and the enthalpy rise
`ṁ cp (T_out - T_in) = ∫ q'`. With the prescribed film law `h_film P (T_clad - T) = q'` on the
heated perimeter `P`, the clad surface temperature satisfies `T_clad ≤ T_out + q₀ / (h_film P)`; a
mass-flow floor `ṁ ≥ ṁ_min > 0` makes the outlet value at `ṁ_min` a bound for every admissible flow.

Model inputs of section D: the power shape and the film law are prescribed, not derived; nothing
here is a boiling, critical-heat-flux or safety result. Blocked flow (`ṁ = 0`) has no steady
solution under positive heating, while Lean's `x / 0 = 0` would turn the outlet formula into `T_in`,
so the results assume `ṁ > 0`. Each result assumes only the hypotheses its proof uses.

## ii. Key results

- `HeatTransfer.outwardFluxSum`: the outward conductive fluxes at the
  two faces sum to `H * L`.
- `HeatTransfer.slabTemperature_le_midplane`: for equal surface
  temperatures and `H ≥ 0`, the profile on the slab is at most the
  midplane value `Ts + H * L^2 / (8k)`.
- `HeatTransfer.cylinder_radial_equation` and
  `HeatTransfer.cylinder_outwardPower_of_pos`: on the physical
  domain `0 < r ≤ R` with `0 < R` and `0 < k`, the regular
  heated-cylinder profile satisfies the radial heat-balance
  equation away from the center, and its outward power per unit
  length is `π * R^2 * qvol`. The unrestricted algebraic form of
  the radial identity is `cylinder_radial_equation_algebraic`.
- `HeatTransfer.isSteadyCoolantProfile_coolantTemperature` and
  `HeatTransfer.IsSteadyCoolantProfile.eq_coolantTemperature`: the integrated coolant profile
  solves the steady balance and is its only solution on the heated length.
- `HeatTransfer.IsSteadyCoolantProfile.outlet` and
  `HeatTransfer.IsSteadyCoolantProfile.enthalpy_rise`: the outlet temperature and the enthalpy
  rise `ṁ cp (T_out - T_in) = ∫ q' = 2 q₀ Lₑ sin (π L / (2 Lₑ)) / π`.
- `HeatTransfer.IsSteadyCoolantProfile.clad_le`: the clad-temperature envelope
  `T_clad ≤ T_out + q₀ / (h_film P)`.

## iii. Table of contents

- A. Slab profile and outward fluxes
- B. Derivative bridge to the geotherm profile
- C. Regular heated cylinder
- D. Coolant channel with a cosine power profile
  - D.1. Power shape and the steady coolant profile
  - D.2. Outlet temperature and enthalpy rise
  - D.3. Clad-temperature envelope

## iv. References

- `EarthScience.geotherm_hasDerivAt`, `EarthScience.geotherm_second_deriv`
  and `EarthScience.geotherm_boundary` in
  `PhyslibExt.EarthScience.ConductiveGeotherm`, whose profile this file
  instantiates.
- F. P. Incropera, D. P. DeWitt, T. L. Bergman, and A. S. Lavine,
  *Fundamentals of Heat and Mass Transfer*, 6th edition (Wiley, 2007),
  Section 3.7: one-dimensional, steady-state conduction in radial
  systems with uniform volumetric energy generation. For a solid
  cylinder of radius `R`, conductivity `k`, and generation rate
  `qvol` with surface held at `Ts`, the temperature distribution is
  `T(r) = Ts + (qvol * R^2 / (4 * k)) * (1 - (r / R)^2)` on
  `0 ≤ r ≤ R`; integrating the generation over the cross-section
  gives the surface balance `2πR * (-k * T'(R)) = π * R^2 * qvol`
  per unit length.
- N. E. Todreas and M. S. Kazimi, *Nuclear Systems I: Thermal Hydraulic Fundamentals*, Taylor &
  Francis, ch. 13: the chopped-cosine linear heat rate `q'(z) = q₀' cos (π z / Lₑ)` over the
  heated length, the coolant temperature rise
  `T(z) - T_in = q₀' Lₑ (sin (π z / Lₑ) + sin (π L / (2 Lₑ))) / (π ṁ cp)` and the clad surface
  temperature from the film coefficient.
- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, 6th ed., Wiley (2007), Section 8.3: the internal-flow energy balance
  `ṁ cp dTm / dx = q'' P`.

## A. Slab profile and outward fluxes

-/

@[expose] public section

namespace HeatTransfer

/-- Temperature profile of the steady one-dimensional slab with constant
conductivity and uniform volumetric heat source `H`: on a slab of
thickness `L` with surface temperatures `Ts` and `Tb`,
`T(d) = Ts + ((Tb - Ts) / L + H * L / (2k)) * d - H * d^2 / (2k)`. This is
the existing geotherm profile shape read as a slab model; `H` is an
externally supplied heat source. It is intended for `L ≠ 0`, `k ≠ 0`. -/
noncomputable def slabTemperature (Ts Tb L k H d : ℝ) : ℝ :=
  Ts + ((Tb - Ts) / L + H * L / (2 * k)) * d - H * d ^ 2 / (2 * k)

/-- Temperature gradient of the slab profile,
`T'(d) = (Tb - Ts) / L + H * L / (2k) - H * d / k`. -/
noncomputable def slabGradient (Ts Tb L k H d : ℝ) : ℝ :=
  (Tb - Ts) / L + H * L / (2 * k) - H * d / k

/-- Left surface value of the slab profile. -/
lemma slabTemperature_zero (Ts Tb L k H : ℝ) : slabTemperature Ts Tb L k H 0 = Ts := by
  simp [slabTemperature]

/-- Right surface value of the slab profile. -/
lemma slabTemperature_length {Ts Tb L k H : ℝ} (hL : L ≠ 0) (hk : k ≠ 0) :
    slabTemperature Ts Tb L k H L = Tb := by
  unfold slabTemperature
  have hk2 : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk
  field_simp
  ring

/-- Total outward heat removal per unit area from both slab faces:
`(k * T'(0)) - (k * T'(L)) = H * L`. The conductive flux in this
coordinate is `-k * T'`, so the two terms are the outward fluxes at the
left and right faces; their sum balances the uniform source integrated
over the thickness. -/
lemma outwardFluxSum {Ts Tb L k H : ℝ} (hk : k ≠ 0) :
    k * slabGradient Ts Tb L k H 0 - k * slabGradient Ts Tb L k H L = H * L := by
  unfold slabGradient
  simp only [mul_zero, zero_div, sub_zero]
  generalize (Tb - Ts) / L = Y
  have hk2 : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk
  field_simp
  ring

/-- Equal surface temperatures: the midplane temperature is
`Ts + H * L^2 / (8k)`. -/
lemma slabTemperature_midplane {Ts L k H : ℝ} (hk : k ≠ 0) :
    slabTemperature Ts Ts L k H (L / 2) = Ts + H * L ^ 2 / (8 * k) := by
  unfold slabTemperature
  simp only [sub_self, zero_div, zero_add]
  have hk2 : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk
  have hk8 : (8 : ℝ) * k ≠ 0 := mul_ne_zero (by norm_num) hk
  field_simp
  ring

/-- Equal surface temperatures with nonnegative source: the midplane is
the maximum of the profile on the slab, and its value is the midplane
temperature above. -/
lemma slabTemperature_le_midplane {Ts L k H d : ℝ} (hk : 0 < k)
    (hH : 0 ≤ H) (hd0 : 0 ≤ d) (hdL : d ≤ L) :
    slabTemperature Ts Ts L k H d ≤ Ts + H * L ^ 2 / (8 * k) := by
  have _ := hd0
  have _ := hdL
  unfold slabTemperature
  simp only [sub_self, zero_div, zero_add]
  have hk' : k ≠ 0 := ne_of_gt hk
  have hk2 : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk'
  have hk8 : (8 : ℝ) * k ≠ 0 := mul_ne_zero (by norm_num) hk'
  have h8k : (0 : ℝ) < 8 * k := mul_pos (by norm_num) hk
  have key : Ts + H * L ^ 2 / (8 * k)
      - (Ts + H * L / (2 * k) * d - H * d ^ 2 / (2 * k))
      = H * (L - 2 * d) ^ 2 / (8 * k) := by
    field_simp
    ring
  have hnonneg : (0 : ℝ) ≤ H * (L - 2 * d) ^ 2 / (8 * k) :=
    div_nonneg (mul_nonneg hH (sq_nonneg _)) (le_of_lt h8k)
  linarith



/-! ## B. Derivative bridge to the geotherm profile -/

/-- The slab gradient is the actual derivative of the slab temperature:
this is `EarthScience.geotherm_hasDerivAt` for the same profile. -/
lemma slabTemperature_hasDerivAt {Ts Tb L k H d : ℝ} :
    HasDerivAt (slabTemperature Ts Tb L k H) (slabGradient Ts Tb L k H d) d :=
  EarthScience.geotherm_hasDerivAt

/-- The slab gradient itself has derivative `-H / k`, and the steady
balance `k * T'' + H = 0` holds: `EarthScience.geotherm_second_deriv`
for the same profile. -/
lemma slabGradient_hasDerivAt {Ts Tb L k H d : ℝ} (hk : 0 < k) :
    HasDerivAt (slabGradient Ts Tb L k H) (-H / k) d ∧ k * (-H / k) + H = 0 :=
  EarthScience.geotherm_second_deriv hk

/-! ## C. Regular heated cylinder -/

/-- Temperature profile of the steady solid cylinder with constant
conductivity `k` and uniform volumetric heat source `qvol`: at radius
`r` in a cylinder of radius `R` with surface temperature `Ts`,
`T(r) = Ts + qvol * (R^2 - r^2) / (4k)`. This is the regular polynomial
profile; at `r = 0` it is read through its polynomial extension, not by
evaluating a radial flux divided by `r`. Intended for `k ≠ 0`; the
physical profile is the restriction to `0 ≤ r ≤ R` with `0 < R`. -/
noncomputable def cylinderTemperature (Ts R k qvol r : ℝ) : ℝ :=
  Ts + qvol * (R ^ 2 - r ^ 2) / (4 * k)

/-- Radial temperature gradient of the cylinder profile,
`T'(r) = -qvol * r / (2k)`. -/
noncomputable def cylinderGradient (k qvol r : ℝ) : ℝ :=
  -qvol * r / (2 * k)

private lemma hasDerivAt_quad {c d x : ℝ} :
    HasDerivAt (fun s : ℝ => c * s ^ 2 + d) (2 * c * x) x := by
  have h := ((hasDerivAt_pow 2 x).const_mul c).add_const d
  convert h using 1
  ring

/-- Center value: `T(0) = Ts + qvol * R^2 / (4k)`. -/
lemma cylinderTemperature_center {Ts R k qvol : ℝ} :
    cylinderTemperature Ts R k qvol 0 = Ts + qvol * R ^ 2 / (4 * k) := by
  simp [cylinderTemperature]

/-- Surface value: `T(R) = Ts`. -/
lemma cylinderTemperature_surface (Ts R k qvol : ℝ) :
    cylinderTemperature Ts R k qvol R = Ts := by
  simp [cylinderTemperature]

/-- Center-to-surface temperature rise: `qvol * R^2 / (4k)`. -/
lemma cylinder_center_sub_surface {Ts R k qvol : ℝ} :
    cylinderTemperature Ts R k qvol 0 - cylinderTemperature Ts R k qvol R =
      qvol * R ^ 2 / (4 * k) := by
  rw [cylinderTemperature_center, cylinderTemperature_surface]
  ring

/-- The gradient vanishes at the center: the regular profile has zero
radial slope at `r = 0`. -/
lemma cylinderGradient_zero (k qvol : ℝ) : cylinderGradient k qvol 0 = 0 := by
  simp [cylinderGradient]

/-- Derivative of the cylinder profile is the stated gradient. -/
lemma hasDerivAt_cylinderTemperature {Ts R k qvol r : ℝ} (hk : k ≠ 0) :
    HasDerivAt (cylinderTemperature Ts R k qvol) (cylinderGradient k qvol r) r := by
  have h2k : (2 : ℝ) * k ≠ 0 := mul_ne_zero (by norm_num) hk
  have h4k : (4 : ℝ) * k ≠ 0 := mul_ne_zero (by norm_num) hk
  have hbase : HasDerivAt (fun s : ℝ => (-(qvol / (4 * k))) * s ^ 2 + (Ts + qvol * R ^ 2 / (4 * k)))
      (2 * (-(qvol / (4 * k))) * r) r := hasDerivAt_quad
  have hfun : (fun s : ℝ => (-(qvol / (4 * k))) * s ^ 2 + (Ts + qvol * R ^ 2 / (4 * k)))
      = cylinderTemperature Ts R k qvol := by
    funext s
    simp only [cylinderTemperature]
    field_simp
    ring
  have hderiv : 2 * (-(qvol / (4 * k))) * r = cylinderGradient k qvol r := by
    simp only [cylinderGradient]
    field_simp
    ring
  rw [hfun, hderiv] at hbase
  exact hbase

/-- Algebraic radial identity for the polynomial extension of the
cylinder profile: for any `r > 0` and `k ≠ 0`,
`(1 / r) * (d/dr) (r * T'(r)) = -qvol / k`, the cylindrical
Laplacian of the extended profile. This is not restricted to the
physical cylinder; the physical statement is
`cylinder_radial_equation`. -/
lemma cylinder_radial_equation_algebraic {k qvol r : ℝ} (hk : k ≠ 0)
    (hr : 0 < r) :
    (1 / r) * deriv (fun s : ℝ => s * cylinderGradient k qvol s) r =
      -qvol / k := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have h2k : (2 : ℝ) * k ≠ 0 := mul_ne_zero (by norm_num) hk
  have hbase : HasDerivAt (fun s : ℝ => (-(qvol / (2 * k))) * s ^ 2 + 0)
      (2 * (-(qvol / (2 * k))) * r) r := hasDerivAt_quad
  have hfun : (fun s : ℝ => (-(qvol / (2 * k))) * s ^ 2 + 0)
      = (fun s : ℝ => s * cylinderGradient k qvol s) := by
    funext s
    simp only [cylinderGradient]
    field_simp
    ring
  have hderiv_val : 2 * (-(qvol / (2 * k))) * r = -qvol * r / k := by
    field_simp
  rw [hfun, hderiv_val] at hbase
  have hderiv := hbase.deriv
  rw [hderiv]
  field_simp

/-- Radial heat-balance equation on the physical cylinder: for
radius `0 < R`, conductivity `0 < k`, and an interior radius
`0 < r` with `r ≤ R`,
`(1 / r) * (d/dr) (r * T'(r)) = -qvol / k`. -/
theorem cylinder_radial_equation {R k qvol r : ℝ} (hR : 0 < R)
    (hk : 0 < k) (hr : 0 < r) (hrR : r ≤ R) :
    (1 / r) * deriv (fun s : ℝ => s * cylinderGradient k qvol s) r =
      -qvol / k :=
  cylinder_radial_equation_algebraic (ne_of_gt hk) hr

/-- Algebraic form of the surface-power identity:
`2πR * (-k * T'(R)) = π * R^2 * qvol` for any `k ≠ 0`, with no
physical domain assumed on `R` or `k`. -/
lemma cylinder_outwardPower {R k qvol : ℝ} (hk : k ≠ 0) :
    2 * Real.pi * R * (-k * cylinderGradient k qvol R) =
      Real.pi * R ^ 2 * qvol := by
  have h2k : (2 : ℝ) * k ≠ 0 := mul_ne_zero (by norm_num) hk
  simp only [cylinderGradient]
  field_simp

/-- Outward conductive power per unit length at the surface of the
physical cylinder: for radius `0 < R` and conductivity `0 < k`,
`2πR * (-k * T'(R)) = π * R^2 * qvol`, balancing the total source
generated in the cross-section. Here `2πR` is the circumference per
unit length and the profile is the physical solution on
`0 ≤ r ≤ R`. -/
theorem cylinder_outwardPower_of_pos {R k qvol : ℝ} (hR : 0 < R)
    (hk : 0 < k) :
    2 * Real.pi * R * (-k * cylinderGradient k qvol R) =
      Real.pi * R ^ 2 * qvol :=
  cylinder_outwardPower (ne_of_gt hk)

/-! ## D. Coolant channel with a cosine power profile -/

/-! ### D.1. Power shape and the steady coolant profile -/

/-- Chopped-cosine linear power `q'(z) = q₀ * cos (π z / Lₑ)` (power per unit length) at axial
position `z`, with peak `q₀` at the midplane and extrapolated length `Lₑ`; a prescribed model
input. Intended for `Lₑ > 0`; on the heated length `[-L/2, L/2]` with `L ≤ Lₑ` its values lie in
`[0, q₀]` for `q₀ ≥ 0`. -/
noncomputable def cosineLinearPower (q0 Le z : ℝ) : ℝ := q0 * Real.cos (Real.pi * z / Le)

/-- `T` is a steady coolant temperature on the heated length `[-L/2, L/2]` with inlet value
`Tin`: `T (-L/2) = Tin`, and at every point of the heated length `T` is differentiable with
`ṁ * cp * T' = q'`. -/
def IsSteadyCoolantProfile (mdot cp q0 Le L Tin : ℝ) (T : ℝ → ℝ) : Prop :=
  T (-(L / 2)) = Tin ∧ ∀ z ∈ Set.Icc (-(L / 2)) (L / 2),
    DifferentiableAt ℝ T z ∧ mdot * cp * deriv T z = cosineLinearPower q0 Le z

/-- Coolant temperature obtained by integrating `ṁ * cp * T' = q'` from the inlet:
`T(z) = Tin + q₀ Lₑ (sin (π z / Lₑ) + sin (π L / (2 Lₑ))) / (π ṁ cp)`. Intended for `ṁ > 0`,
`cp > 0`, `Lₑ > 0`. -/
noncomputable def coolantTemperature (mdot cp q0 Le L Tin z : ℝ) : ℝ :=
  Tin + q0 * Le * (Real.sin (Real.pi * z / Le) + Real.sin (Real.pi * L / (2 * Le))) /
    (Real.pi * mdot * cp)

/-- Coolant outlet temperature `Tout = Tin + 2 q₀ Lₑ sin (π L / (2 Lₑ)) / (π ṁ cp)`. Intended for
`ṁ > 0` and `cp > 0`; at `ṁ = 0` Lean's `x / 0 = 0` gives the junk value `Tin`, while blocked flow
has no steady state (`fixture_blocked_flow`). -/
noncomputable def coolantOutletTemp (mdot cp q0 Le L Tin : ℝ) : ℝ :=
  Tin + 2 * q0 * Le * Real.sin (Real.pi * L / (2 * Le)) / (Real.pi * mdot * cp)

private lemma hasDerivAt_sin_pi_div (Le x : ℝ) :
    HasDerivAt (fun z => Real.sin (Real.pi * z / Le))
      (Real.cos (Real.pi * x / Le) * (Real.pi / Le)) x := by
  have hi : HasDerivAt (fun z => Real.pi * z / Le) (Real.pi / Le) x := by
    have h := ((hasDerivAt_id' x).const_mul Real.pi).div_const Le
    simpa using h
  exact hi.sin

private lemma continuous_cosineLinearPower (q0 Le : ℝ) :
    Continuous (cosineLinearPower q0 Le) := by
  unfold cosineLinearPower
  fun_prop

private lemma steady_integral_aux {mdot cp q0 Le L Tin : ℝ} {T : ℝ → ℝ}
    (hT : IsSteadyCoolantProfile mdot cp q0 Le L Tin T)
    {a b : ℝ} (hab : a ≤ b) (ha : -(L / 2) ≤ a) (hb : b ≤ L / 2) :
    ∫ w in a..b, cosineLinearPower q0 Le w = mdot * cp * T b - mdot * cp * T a := by
  have hmem : ∀ x ∈ Set.uIcc a b, x ∈ Set.Icc (-(L / 2)) (L / 2) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun w => mdot * cp * T w) (cosineLinearPower q0 Le x) x := by
    intro x hx
    obtain ⟨hdiff, hbal⟩ := hT.2 x (hmem x hx)
    have hcm : HasDerivAt (fun w => mdot * cp * T w) (mdot * cp * deriv T x) x :=
      hdiff.hasDerivAt.const_mul (mdot * cp)
    rwa [hbal] at hcm
  have hint : IntervalIntegrable (cosineLinearPower q0 Le) MeasureTheory.volume a b :=
    (continuous_cosineLinearPower q0 Le).intervalIntegrable a b
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- On the heated length, with `0 < L ≤ Lₑ` and `q₀ ≥ 0`, the linear power lies in `[0, q₀]`. -/
lemma cosineLinearPower_mem_Icc {q0 Le L z : ℝ} (hq0 : 0 ≤ q0) (hL : 0 < L) (hLLe : L ≤ Le)
    (hz : z ∈ Set.Icc (-(L / 2)) (L / 2)) :
    0 ≤ cosineLinearPower q0 Le z ∧ cosineLinearPower q0 Le z ≤ q0 := by
  obtain ⟨hz1, hz2⟩ := hz
  have hLe : 0 < Le := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have h3 : Real.pi * L ≤ Real.pi * Le := mul_le_mul_of_nonneg_left hLLe hpi.le
  have hlo : -(Real.pi / 2) ≤ Real.pi * z / Le := by
    rw [le_div_iff₀ hLe]
    have h1 : Real.pi * (-(L / 2)) ≤ Real.pi * z :=
      mul_le_mul_of_nonneg_left hz1 hpi.le
    linarith [h1, h3]
  have hhi : Real.pi * z / Le ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hLe]
    have h1 : Real.pi * z ≤ Real.pi * (L / 2) :=
      mul_le_mul_of_nonneg_left hz2 hpi.le
    linarith [h1, h3]
  have hcos : 0 ≤ Real.cos (Real.pi * z / Le) :=
    Real.cos_nonneg_of_mem_Icc ⟨hlo, hhi⟩
  simp only [cosineLinearPower]
  constructor
  · exact mul_nonneg hq0 hcos
  · calc q0 * Real.cos (Real.pi * z / Le) ≤ q0 * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_le_one _) hq0
        _ = q0 := mul_one q0

/-- Integral of the chopped-cosine power:
`∫ z in a..b, q'(z) = q₀ Lₑ (sin (π b / Lₑ) - sin (π a / Lₑ)) / π` for `Lₑ ≠ 0`. -/
lemma integral_cosineLinearPower {q0 Le : ℝ} (hLe : Le ≠ 0) (a b : ℝ) :
    ∫ z in a..b, cosineLinearPower q0 Le z =
      q0 * Le * (Real.sin (Real.pi * b / Le) - Real.sin (Real.pi * a / Le)) / Real.pi := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun z => q0 * Le * Real.sin (Real.pi * z / Le) / Real.pi)
        (cosineLinearPower q0 Le x) x := by
    intro x _
    have hs := hasDerivAt_sin_pi_div Le x
    have hcm : HasDerivAt (fun z => (q0 * Le) * Real.sin (Real.pi * z / Le))
        ((q0 * Le) * (Real.cos (Real.pi * x / Le) * (Real.pi / Le))) x :=
      hs.const_mul (q0 * Le)
    have hdv := hcm.div_const Real.pi
    have hval : (q0 * Le) * (Real.cos (Real.pi * x / Le) * (Real.pi / Le)) / Real.pi =
        cosineLinearPower q0 Le x := by
      simp only [cosineLinearPower]
      field_simp
    rwa [hval] at hdv
  have hint : IntervalIntegrable (cosineLinearPower q0 Le) MeasureTheory.volume a b :=
    (continuous_cosineLinearPower q0 Le).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  refine hFTC.trans ?_
  change q0 * Le * Real.sin (Real.pi * b / Le) / Real.pi -
      q0 * Le * Real.sin (Real.pi * a / Le) / Real.pi = _
  ring

/-- **Existence.** The integrated profile is a steady coolant profile with inlet value `Tin`, for
`ṁ, cp, Lₑ > 0`. -/
lemma isSteadyCoolantProfile_coolantTemperature {mdot cp Le : ℝ} (hm : 0 < mdot) (hcp : 0 < cp)
    (hLe : 0 < Le) (q0 L Tin : ℝ) :
    IsSteadyCoolantProfile mdot cp q0 Le L Tin (coolantTemperature mdot cp q0 Le L Tin) := by
  have hLe' : Le ≠ 0 := ne_of_gt hLe
  have h2Le : (2 : ℝ) * Le ≠ 0 := mul_ne_zero two_ne_zero hLe'
  have hD : Real.pi * mdot * cp ≠ 0 :=
    ne_of_gt (by positivity : (0 : ℝ) < Real.pi * mdot * cp)
  have harg : Real.pi * (-(L / 2)) / Le = -(Real.pi * L / (2 * Le)) := by
    field_simp
  refine ⟨?_, ?_⟩
  · unfold coolantTemperature
    rw [harg, Real.sin_neg, neg_add_cancel]
    simp
  · intro z _
    have hs := hasDerivAt_sin_pi_div Le z
    have h2 : HasDerivAt
        (fun z => Real.sin (Real.pi * z / Le) + Real.sin (Real.pi * L / (2 * Le)))
        (Real.cos (Real.pi * z / Le) * (Real.pi / Le)) z := by
      have h := hs.add (hasDerivAt_const z (Real.sin (Real.pi * L / (2 * Le))))
      rw [add_zero] at h
      exact h
    have h3 : HasDerivAt
        (fun z => (q0 * Le) *
          (Real.sin (Real.pi * z / Le) + Real.sin (Real.pi * L / (2 * Le))))
        ((q0 * Le) * (Real.cos (Real.pi * z / Le) * (Real.pi / Le))) z :=
      h2.const_mul (q0 * Le)
    have h4 : HasDerivAt
        (fun z => (q0 * Le) *
          (Real.sin (Real.pi * z / Le) + Real.sin (Real.pi * L / (2 * Le))) /
          (Real.pi * mdot * cp))
        (((q0 * Le) * (Real.cos (Real.pi * z / Le) * (Real.pi / Le))) /
          (Real.pi * mdot * cp)) z :=
      h3.div_const (Real.pi * mdot * cp)
    have h5 : HasDerivAt (coolantTemperature mdot cp q0 Le L Tin)
        (((q0 * Le) * (Real.cos (Real.pi * z / Le) * (Real.pi / Le))) /
          (Real.pi * mdot * cp)) z := by
      have h := (hasDerivAt_const z Tin).add h4
      rw [zero_add] at h
      unfold coolantTemperature
      exact h
    refine ⟨h5.differentiableAt, ?_⟩
    rw [h5.deriv]
    simp only [cosineLinearPower]
    field_simp

/-- **Integration.** Every steady coolant profile with inlet value `Tin` is the integrated profile
on the heated length, for `ṁ, cp, Lₑ > 0`. -/
lemma IsSteadyCoolantProfile.eq_coolantTemperature {mdot cp q0 Le L Tin : ℝ} {T : ℝ → ℝ}
    (hm : 0 < mdot) (hcp : 0 < cp) (hLe : 0 < Le)
    (hT : IsSteadyCoolantProfile mdot cp q0 Le L Tin T) :
    ∀ z ∈ Set.Icc (-(L / 2)) (L / 2), T z = coolantTemperature mdot cp q0 Le L Tin z := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hLe' : Le ≠ 0 := ne_of_gt hLe
  have h2Le : (2 : ℝ) * Le ≠ 0 := mul_ne_zero two_ne_zero hLe'
  have harg : Real.pi * (-(L / 2)) / Le = -(Real.pi * L / (2 * Le)) := by
    field_simp
  intro z hz
  have hS := steady_integral_aux hT hz.1 (le_refl _) hz.2
  rw [hT.1] at hS
  have hC := integral_cosineLinearPower (q0 := q0) hLe' (-(L / 2)) z
  rw [hC, harg, Real.sin_neg, sub_neg_eq_add] at hS
  have hk : mdot * cp * (T z - Tin) =
      q0 * Le * (Real.sin (Real.pi * z / Le) + Real.sin (Real.pi * L / (2 * Le))) /
        Real.pi := by
    linarith [hS]
  have h1 : (mdot * cp * (T z - Tin)) * Real.pi =
      q0 * Le * (Real.sin (Real.pi * z / Le) + Real.sin (Real.pi * L / (2 * Le))) := by
    rw [hk]
    exact div_mul_cancel₀ _ hpi
  have key : (T z - Tin) * (Real.pi * mdot * cp) =
      q0 * Le * (Real.sin (Real.pi * z / Le) + Real.sin (Real.pi * L / (2 * Le))) := by
    linear_combination h1
  have hD : (0 : ℝ) < Real.pi * mdot * cp := by positivity
  have hfinal : T z - Tin =
      q0 * Le * (Real.sin (Real.pi * z / Le) + Real.sin (Real.pi * L / (2 * Le))) /
        (Real.pi * mdot * cp) := by
    rw [eq_div_iff (ne_of_gt hD)]
    exact key
  unfold coolantTemperature
  rw [← hfinal]
  ring

/-! ### D.2. Outlet temperature and enthalpy rise -/

/-- **Outlet temperature.** A steady coolant profile on `[-L/2, L/2]` with `0 < L ≤ Lₑ` leaves at
`T(L/2) = Tin + 2 q₀ Lₑ sin (π L / (2 Lₑ)) / (π ṁ cp)`. -/
lemma IsSteadyCoolantProfile.outlet {mdot cp q0 Le L Tin : ℝ} {T : ℝ → ℝ} (hm : 0 < mdot)
    (hcp : 0 < cp) (hL : 0 < L) (hLLe : L ≤ Le)
    (hT : IsSteadyCoolantProfile mdot cp q0 Le L Tin T) :
    T (L / 2) = coolantOutletTemp mdot cp q0 Le L Tin := by
  have hLe : 0 < Le := by linarith
  have hmem : L / 2 ∈ Set.Icc (-(L / 2)) (L / 2) := ⟨by linarith, le_refl _⟩
  have heq := IsSteadyCoolantProfile.eq_coolantTemperature hm hcp hLe hT (L / 2) hmem
  rw [heq]
  unfold coolantTemperature coolantOutletTemp
  have hLe' : Le ≠ 0 := ne_of_gt hLe
  have h2Le : (2 : ℝ) * Le ≠ 0 := mul_ne_zero two_ne_zero hLe'
  have harg : Real.pi * (L / 2) / Le = Real.pi * L / (2 * Le) := by
    field_simp
  rw [harg]
  ring

/-- **Enthalpy rise.** The coolant enthalpy rise between the ports equals the integrated linear
power: `ṁ cp (T(L/2) - Tin) = ∫ q' = 2 q₀ Lₑ sin (π L / (2 Lₑ)) / π`. -/
lemma IsSteadyCoolantProfile.enthalpy_rise {mdot cp q0 Le L Tin : ℝ} {T : ℝ → ℝ}
    (hm : 0 < mdot) (hcp : 0 < cp) (hL : 0 < L) (hLLe : L ≤ Le)
    (hT : IsSteadyCoolantProfile mdot cp q0 Le L Tin T) :
    mdot * cp * (T (L / 2) - Tin) = ∫ z in -(L / 2)..L / 2, cosineLinearPower q0 Le z ∧
      ∫ z in -(L / 2)..L / 2, cosineLinearPower q0 Le z =
        2 * q0 * Le * Real.sin (Real.pi * L / (2 * Le)) / Real.pi := by
  have hLe : 0 < Le := by linarith
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have _ := hm
  have _ := hcp
  constructor
  · have hS := steady_integral_aux hT hle (le_refl _) (le_refl _)
    rw [hT.1] at hS
    rw [hS]
    ring
  · have hLe' : Le ≠ 0 := ne_of_gt hLe
    have h2Le : (2 : ℝ) * Le ≠ 0 := mul_ne_zero two_ne_zero hLe'
    have hC := integral_cosineLinearPower (q0 := q0) hLe' (-(L / 2)) (L / 2)
    rw [hC]
    have harg1 : Real.pi * (L / 2) / Le = Real.pi * L / (2 * Le) := by
      field_simp
    have harg2 : Real.pi * (-(L / 2)) / Le = -(Real.pi * L / (2 * Le)) := by
      field_simp
    rw [harg1, harg2, Real.sin_neg, sub_neg_eq_add]
    ring

/-- **Uniform envelope from the mass-flow floor.** For `ṁ ≥ ṁ_min > 0`, `cp > 0`, `q₀ ≥ 0` and
`0 < L ≤ Lₑ`, the outlet temperature is at most its value at `ṁ_min`. -/
lemma coolantOutletTemp_le_of_le_mdot {mdotMin mdot cp q0 Le L : ℝ} (hmin : 0 < mdotMin)
    (hmdot : mdotMin ≤ mdot) (hcp : 0 < cp) (hq0 : 0 ≤ q0) (hL : 0 < L) (hLLe : L ≤ Le)
    (Tin : ℝ) :
    coolantOutletTemp mdot cp q0 Le L Tin ≤ coolantOutletTemp mdotMin cp q0 Le L Tin := by
  have hLe : 0 < Le := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin : 0 ≤ Real.sin (Real.pi * L / (2 * Le)) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Le)]
      exact mul_le_mul_of_nonneg_left (by linarith) hpi.le
  have hnum : 0 ≤ 2 * q0 * Le * Real.sin (Real.pi * L / (2 * Le)) := by positivity
  have hDmin : 0 < Real.pi * mdotMin * cp := by positivity
  have hDle : Real.pi * mdotMin * cp ≤ Real.pi * mdot * cp := by
    have hpc : 0 < Real.pi * cp := by positivity
    have h := mul_le_mul_of_nonneg_right hmdot (le_of_lt hpc)
    calc Real.pi * mdotMin * cp = mdotMin * (Real.pi * cp) := by ring
      _ ≤ mdot * (Real.pi * cp) := h
      _ = Real.pi * mdot * cp := by ring
  unfold coolantOutletTemp
  exact add_le_add_right (div_le_div_of_nonneg_left hnum hDmin hDle) Tin

/-! ### D.3. Clad-temperature envelope -/

/-- With `q₀ ≥ 0` and `0 < L ≤ Lₑ` the coolant warms monotonically, so on the heated length
every steady profile stays at or below the outlet temperature. -/
lemma IsSteadyCoolantProfile.le_outlet {mdot cp q0 Le L Tin : ℝ} {T : ℝ → ℝ} (hm : 0 < mdot)
    (hcp : 0 < cp) (hq0 : 0 ≤ q0) (hL : 0 < L) (hLLe : L ≤ Le)
    (hT : IsSteadyCoolantProfile mdot cp q0 Le L Tin T) :
    ∀ z ∈ Set.Icc (-(L / 2)) (L / 2), T z ≤ coolantOutletTemp mdot cp q0 Le L Tin := by
  intro z hz
  have hout := IsSteadyCoolantProfile.outlet hm hcp hL hLLe hT
  rw [← hout]
  have hS := steady_integral_aux hT hz.2 hz.1 (le_refl _)
  have hnonneg : 0 ≤ ∫ w in z..L / 2, cosineLinearPower q0 Le w := by
    apply intervalIntegral.integral_nonneg hz.2
    intro x hx
    exact (cosineLinearPower_mem_Icc hq0 hL hLLe ⟨le_trans hz.1 hx.1, hx.2⟩).1
  rw [hS] at hnonneg
  have hmc : 0 < mdot * cp := by positivity
  have h2 : mdot * cp * T z ≤ mdot * cp * T (L / 2) := by linarith [hnonneg]
  exact le_of_mul_le_mul_left h2 hmc

/-- **Clad-temperature envelope.** If the clad surface temperature obeys the prescribed film law
`h_film * P * (T_clad - T) = q'` with `h_film, P > 0`, then on the heated length
`T_clad ≤ Tout + q₀ / (h_film P)`. -/
lemma IsSteadyCoolantProfile.clad_le {mdot cp q0 Le L Tin hfilm perimeter : ℝ}
    {T Tclad : ℝ → ℝ} (hm : 0 < mdot) (hcp : 0 < cp) (hq0 : 0 ≤ q0) (hL : 0 < L)
    (hLLe : L ≤ Le) (hh : 0 < hfilm) (hP : 0 < perimeter)
    (hT : IsSteadyCoolantProfile mdot cp q0 Le L Tin T)
    (hfilmLaw : ∀ z ∈ Set.Icc (-(L / 2)) (L / 2),
      hfilm * perimeter * (Tclad z - T z) = cosineLinearPower q0 Le z) :
    ∀ z ∈ Set.Icc (-(L / 2)) (L / 2),
      Tclad z ≤ coolantOutletTemp mdot cp q0 Le L Tin + q0 / (hfilm * perimeter) := by
  intro z hz
  have hle := IsSteadyCoolantProfile.le_outlet hm hcp hq0 hL hLLe hT z hz
  have hq := (cosineLinearPower_mem_Icc hq0 hL hLLe hz).2
  have hlaw := hfilmLaw z hz
  have hhp : 0 < hfilm * perimeter := by positivity
  have hsol : Tclad z = T z + cosineLinearPower q0 Le z / (hfilm * perimeter) := by
    have hsub : Tclad z - T z = cosineLinearPower q0 Le z / (hfilm * perimeter) := by
      rw [eq_div_iff (ne_of_gt hhp)]
      linear_combination hlaw
    linarith [hsub]
  rw [hsol]
  have hdiv : cosineLinearPower q0 Le z / (hfilm * perimeter) ≤ q0 / (hfilm * perimeter) :=
    (div_le_div_iff_of_pos_right hhp).mpr hq
  exact add_le_add hle hdiv

end HeatTransfer
