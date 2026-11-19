/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.HenryLaw

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Interphase mass transfer with a Henry equilibrium

## i. Overview

Two distinct transfer quantities share the Henry driving force
`H * p - c`, where `H * p` is the equilibrium liquid concentration under
the Henry convention `c = H * p` of `PhyslibExt.EarthScience.HenryLaw`.
The surface molar flux per unit interfacial area is `k * (H * p - c)`,
with transfer coefficient `k` in length per time. The volumetric
transfer rate per unit volume is `k * a * (H * p - c)`, where `a` is the
interfacial area per unit volume, so `k * a` carries inverse time. The
volumetric rate is `a` times the surface flux, not itself a per-unit-area
flux. Positive values are absorption into the liquid; negative values are
desorption. The same driving-force form appears as the total exchange
rate `J = k * A * (H * p - c)` over interface area `A` in
`PhyslibExt.EarthScience.AirWaterExchange`; the surface flux here is that
rate per unit area. The reciprocal volatility convention `c* = p / H_pc`
is related by `H = 1 / H_pc`, as in
`EarthScience.henry_conversion_reciprocal`.

## ii. Key results

- `MassTransfer.volumetricRate_eq`: the volumetric rate is the specific
  area times the surface flux.
- `MassTransfer.volumetricRate_pos`, `MassTransfer.volumetricRate_neg`,
  and `MassTransfer.volumetricRate_eq_zero_iff`: absorption, desorption,
  and equilibrium signs of the volumetric rate.
- `MassTransfer.volumetricRate_pressure_double`: doubling pressure
  doubles only the equilibrium term.
- `MassTransfer.volumetricRate_volatility_form`: the reciprocal
  volatility convention gives the same rate.

## iii. Table of contents

- A. Surface flux and volumetric rate

## iv. References

- R. B. Bird, W. E. Stewart and E. N. Lightfoot, *Transport Phenomena*,
  2nd ed., Wiley (2002), Chapter 22 (mass-transfer coefficients and
  interfacial area per unit volume).
- `PhyslibExt/EarthScience/HenryLaw.lean`: the Henry conventions and
  their reciprocal conversion, imported here.
- `PhyslibExt/EarthScience/AirWaterExchange.lean`: the same driving force
  as a total exchange rate over an interface area.
-/

@[expose] public section

namespace Engineering.Process.MassTransfer

/-! ## A. Surface flux and volumetric rate -/

/-- Surface molar flux per unit interfacial area, `J = k * (c* - c)` with
equilibrium concentration `c* = H * p` under the declared Henry convention
`c = H * p` (`H` is the concentration/pressure constant `H_cp`). The
coefficient `k` carries units of length per time. Positive `J` is
absorption into the liquid; negative `J` is desorption. -/
def surfaceFlux (k H p c : ℝ) : ℝ :=
  k * (H * p - c)

/-- Volumetric transfer rate per unit volume, `k * a * (c* - c)`, where
`a` is the interfacial area per unit volume, so `k * a` carries units of
inverse time. This is a rate per unit volume, not a per-unit-area flux;
it equals `a` times the surface flux. Positive values are absorption into
the liquid; negative values are desorption. -/
def volumetricRate (k a H p c : ℝ) : ℝ :=
  k * a * (H * p - c)

/-- The volumetric rate is the surface flux scaled by the specific
interfacial area. -/
lemma volumetricRate_eq (k a H p c : ℝ) :
    volumetricRate k a H p c = a * surfaceFlux k H p c := by
  unfold volumetricRate surfaceFlux
  ring

/-- The volumetric rate is the coefficient `k * a` times the driving
force `H * p - c`. -/
lemma volumetricRate_apply (k a H p c : ℝ) :
    volumetricRate k a H p c = k * a * (H * p - c) := by
  rfl

/-- Absorption at the surface: below equilibrium (`c < H * p`), the
surface flux is positive for positive `k`. -/
lemma surfaceFlux_pos {k H p c : ℝ} (hk : 0 < k) (h : c < H * p) :
    0 < surfaceFlux k H p c := by
  unfold surfaceFlux
  exact mul_pos hk (sub_pos.mpr h)

/-- Absorption: below equilibrium (`c < H * p`), the volumetric rate is
positive for positive `k` and `a`. -/
lemma volumetricRate_pos {k a H p c : ℝ} (hk : 0 < k) (ha : 0 < a)
    (h : c < H * p) : 0 < volumetricRate k a H p c := by
  unfold volumetricRate
  exact mul_pos (mul_pos hk ha) (sub_pos.mpr h)

/-- Desorption: above equilibrium (`H * p < c`), the volumetric rate is
negative for positive `k` and `a`; it is not a nonnegative source. -/
lemma volumetricRate_neg {k a H p c : ℝ} (hk : 0 < k) (ha : 0 < a)
    (h : H * p < c) : volumetricRate k a H p c < 0 := by
  unfold volumetricRate
  exact mul_neg_of_pos_of_neg (mul_pos hk ha) (sub_neg.mpr h)

/-- Zero driving force: for positive `k` and `a`, the volumetric rate
vanishes exactly at equilibrium `c = H * p`. -/
lemma volumetricRate_eq_zero_iff {k a H p c : ℝ} (hk : 0 < k) (ha : 0 < a) :
    volumetricRate k a H p c = 0 ↔ c = H * p := by
  unfold volumetricRate
  have hka : k * a ≠ 0 := ne_of_gt (mul_pos hk ha)
  constructor
  · intro h0
    have hsub : H * p - c = 0 := (mul_eq_zero.mp h0).resolve_left hka
    have hc : H * p = c := sub_eq_zero.mp hsub
    exact hc.symm
  · intro hceq
    rw [hceq, sub_self, mul_zero]

/-- Doubling the partial pressure doubles the equilibrium concentration:
the driving force at `2 * p` is `2 * (H * p) - c`. The whole rate does not
double, since `c` is unchanged. -/
lemma volumetricRate_pressure_double (k a H p c : ℝ) :
    volumetricRate k a H (2 * p) c = k * a * (2 * (H * p) - c) := by
  unfold volumetricRate
  ring

/-- Pressure-form conversion: with the volatility convention
`c* = p / H_pc` where `H = 1 / H_pc` (the reciprocal convention of
`EarthScience.henry_conversion_reciprocal`), the same volumetric rate is
`k * a * (p / H_pc - c)`. -/
lemma volumetricRate_volatility_form {k a H H_pc p c : ℝ} (hHpc : H_pc ≠ 0)
    (hH : H = 1 / H_pc) :
    volumetricRate k a H p c = k * a * (p / H_pc - c) := by
  unfold volumetricRate
  rw [hH]
  field_simp

end Engineering.Process.MassTransfer
