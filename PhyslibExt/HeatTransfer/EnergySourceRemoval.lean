/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibExt.EarthScience.ConductiveGeotherm

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Energy source removal: steady slab and heated cylinder with uniform heat generation

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

## iii. Table of contents

- A. Slab profile and outward fluxes
- B. Derivative bridge to the geotherm profile
- C. Regular heated cylinder

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

end HeatTransfer
