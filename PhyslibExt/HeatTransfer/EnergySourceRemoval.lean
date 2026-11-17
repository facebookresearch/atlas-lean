/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PhyslibExt.EarthScience.ConductiveGeotherm

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Energy source removal: steady slab with uniform heat generation

## i. Overview

A steady one-dimensional slab of thickness `L` and constant conductivity
`k` with uniform volumetric heat source `H` (an externally supplied
source term, per unit area fluxes). The temperature profile is the
existing geotherm profile of `PhyslibExt.EarthScience.ConductiveGeotherm`
read as a slab; this file names the slab quantities, proves the total
outward heat removal `H * L`, and identifies the midplane maximum for
equal surface temperatures. No transient behavior is claimed: with the
source cut off (`H = 0`) the steady profile is the constant or linear
steady branch, not an instantaneous prediction.

## ii. Key results

- `HeatTransfer.outwardFluxSum`: the outward conductive fluxes at the
  two faces sum to `H * L`.
- `HeatTransfer.slabTemperature_le_midplane`: for equal surface
  temperatures and `H ≥ 0`, the profile on the slab is at most the
  midplane value `Ts + H * L^2 / (8k)`.

## iii. Table of contents

- A. Slab profile and outward fluxes
- B. Derivative bridge to the geotherm profile

## iv. References

- `EarthScience.geotherm_hasDerivAt`, `EarthScience.geotherm_second_deriv`
  and `EarthScience.geotherm_boundary` in
  `PhyslibExt.EarthScience.ConductiveGeotherm`, whose profile this file
  instantiates.

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

end HeatTransfer
