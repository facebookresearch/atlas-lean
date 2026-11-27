/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.HenryLaw
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
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
- B. Two-film resistance

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

/-! ## B. Two-film resistance -/

/-- Overall liquid-side coefficient `KL` defined by
`1 / KL = 1 / kL + H / kG`: film resistances in series, on a liquid
concentration driving-force basis. -/
noncomputable def overallKL (H kG kL : ℝ) : ℝ :=
  1 / (1 / kL + H / kG)

/-- Overall gas-side coefficient `KG` defined by
`1 / KG = 1 / kG + 1 / (H * kL)`, on a gas partial-pressure driving-force
basis. -/
noncomputable def overallKG (H kG kL : ℝ) : ℝ :=
  1 / (1 / kG + 1 / (H * kL))

set_option linter.unusedVariables false in
/-- The resistance-addition identity for `KL`. -/
lemma overallKL_inv_eq {H kG kL : ℝ} (hH : 0 < H) (hkG : 0 < kG)
    (hkL : 0 < kL) : (overallKL H kG kL)⁻¹ = 1 / kL + H / kG := by
  unfold overallKL
  rw [one_div, inv_inv]

set_option linter.unusedVariables false in
/-- The resistance-addition identity for `KG`. -/
lemma overallKG_inv_eq {H kG kL : ℝ} (hH : 0 < H) (hkG : 0 < kG)
    (hkL : 0 < kL) : (overallKG H kG kL)⁻¹ = 1 / kG + 1 / (H * kL) := by
  unfold overallKG
  rw [one_div, inv_inv]

/-- Both overall coefficients are positive for positive film data. -/
lemma overall_pos {H kG kL : ℝ} (hH : 0 < H) (hkG : 0 < kG) (hkL : 0 < kL) :
    0 < overallKL H kG kL ∧ 0 < overallKG H kG kL := by
  constructor
  · unfold overallKL
    positivity
  · unfold overallKG
    positivity

/-- **Two-film elimination, liquid basis.** Under interfacial equilibrium
and the two film laws, the common flux is
`N = KL * (H * pb - cb)`. -/
theorem twoFilm_overall_KL {H kG kL pb cb pi ci N : ℝ} (hH : 0 < H)
    (hkG : 0 < kG) (hkL : 0 < kL) (heq : ci = H * pi)
    (hG : N = kG * (pb - pi)) (hL : N = kL * (ci - cb)) :
    N = overallKL H kG kL * (H * pb - cb) := by
  have hkG' : kG ≠ 0 := ne_of_gt hkG
  have hkL' : kL ≠ 0 := ne_of_gt hkL
  have hKLne : overallKL H kG kL ≠ 0 := ne_of_gt (overall_pos hH hkG hkL).1
  have hKL : overallKL H kG kL * (1 / kL + H / kG) = 1 := by
    rw [← overallKL_inv_eq hH hkG hkL, mul_inv_cancel₀ hKLne]
  have eL : N / kL = ci - cb := by
    field_simp
    linear_combination hL
  have eG : N / kG = pb - pi := by
    field_simp
    linear_combination hG
  have hNe : N * (1 / kL + H / kG) = H * pb - cb := by
    linear_combination eL + H * eG + heq
  have hfactor : overallKL H kG kL * (N * (1 / kL + H / kG)) = N := by
    linear_combination N * hKL
  rw [hNe] at hfactor
  exact hfactor.symm

/-- **Two-film elimination, gas basis.** Under the same hypotheses, the
common flux is `N = KG * (pb - cb / H)`. -/
theorem twoFilm_overall_KG {H kG kL pb cb pi ci N : ℝ} (hH : 0 < H)
    (hkG : 0 < kG) (hkL : 0 < kL) (heq : ci = H * pi)
    (hG : N = kG * (pb - pi)) (hL : N = kL * (ci - cb)) :
    N = overallKG H kG kL * (pb - cb / H) := by
  have hH' : H ≠ 0 := ne_of_gt hH
  have hkG' : kG ≠ 0 := ne_of_gt hkG
  have hkL' : kL ≠ 0 := ne_of_gt hkL
  have hHkL : H * kL ≠ 0 := mul_ne_zero hH' hkL'
  have hKGne : overallKG H kG kL ≠ 0 := ne_of_gt (overall_pos hH hkG hkL).2
  have hKG : overallKG H kG kL * (1 / kG + 1 / (H * kL)) = 1 := by
    rw [← overallKG_inv_eq hH hkG hkL, mul_inv_cancel₀ hKGne]
  have eG : N / kG = pb - pi := by
    field_simp
    linear_combination hG
  have eLH : N / (H * kL) = (ci - cb) / H := by
    field_simp
    linear_combination hL
  have ecb : (ci - cb) / H = pi - cb / H := by
    rw [heq]
    field_simp
  have hNe : N * (1 / kG + 1 / (H * kL)) = pb - cb / H := by
    linear_combination eG + eLH + ecb
  have hfactor : overallKG H kG kL * (N * (1 / kG + 1 / (H * kL))) = N := by
    linear_combination N * hKG
  rw [hNe] at hfactor
  exact hfactor.symm

set_option linter.unusedVariables false in
/-- Vanishing gas-side resistance: as `kG → ∞`, the liquid-basis overall
coefficient tends to the liquid film coefficient `kL`. -/
theorem tendsto_overallKL_kG_atTop {H kL : ℝ} (hH : 0 < H) (hkL : 0 < kL) :
    Filter.Tendsto (fun kG => overallKL H kG kL) Filter.atTop (nhds kL) := by
  have hkL' : kL ≠ 0 := ne_of_gt hkL
  have h1kL : (1 : ℝ) / kL ≠ 0 := div_ne_zero one_ne_zero hkL'
  have hHkG : Filter.Tendsto (fun kG : ℝ => H / kG) Filter.atTop (nhds (0 : ℝ)) := by
    have h1 : Filter.Tendsto (fun _ : ℝ => H) Filter.atTop (nhds H) :=
      tendsto_const_nhds
    have h2 : Filter.Tendsto (fun kG : ℝ => kG⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_inv_atTop_zero
    have hprod : Filter.Tendsto (fun kG : ℝ => H * kG⁻¹) Filter.atTop (nhds (H * 0)) :=
      h1.mul h2
    rw [mul_zero] at hprod
    simpa [div_eq_mul_inv] using hprod
  have hden : Filter.Tendsto (fun kG : ℝ => 1 / kL + H / kG) Filter.atTop
      (nhds ((1 : ℝ) / kL)) := by
    have h1 : Filter.Tendsto (fun _ : ℝ => (1 : ℝ) / kL) Filter.atTop
        (nhds ((1 : ℝ) / kL)) := tendsto_const_nhds
    have hadd := h1.add hHkG
    simpa using hadd
  have hinv := hden.inv₀ h1kL
  have hlim : ((1 : ℝ) / kL)⁻¹ = kL := by rw [one_div, inv_inv]
  unfold overallKL
  simpa [one_div, hlim] using hinv

set_option linter.unusedVariables false in
/-- Vanishing liquid-side resistance: as `kL → ∞`, the gas-basis overall
coefficient tends to the gas film coefficient `kG`. -/
theorem tendsto_overallKG_kL_atTop {H kG : ℝ} (hH : 0 < H) (hkG : 0 < kG) :
    Filter.Tendsto (fun kL => overallKG H kG kL) Filter.atTop (nhds kG) := by
  have hkG' : kG ≠ 0 := ne_of_gt hkG
  have h1kG : (1 : ℝ) / kG ≠ 0 := div_ne_zero one_ne_zero hkG'
  have hzero : Filter.Tendsto (fun kL : ℝ => 1 / (H * kL)) Filter.atTop (nhds (0 : ℝ)) := by
    have h1 : Filter.Tendsto (fun _ : ℝ => (1 : ℝ) / H) Filter.atTop (nhds ((1 : ℝ) / H)) :=
      tendsto_const_nhds
    have h2 : Filter.Tendsto (fun kL : ℝ => kL⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_inv_atTop_zero
    have hprod : Filter.Tendsto (fun kL : ℝ => (1 / H) * kL⁻¹) Filter.atTop
        (nhds ((1 : ℝ) / H * 0)) := h1.mul h2
    rw [mul_zero] at hprod
    simpa only [one_div, mul_inv] using hprod
  have hden : Filter.Tendsto (fun kL : ℝ => 1 / kG + 1 / (H * kL)) Filter.atTop
      (nhds ((1 : ℝ) / kG)) := by
    have h1 : Filter.Tendsto (fun _ : ℝ => (1 : ℝ) / kG) Filter.atTop
        (nhds ((1 : ℝ) / kG)) := tendsto_const_nhds
    have hadd := h1.add hzero
    simpa using hadd
  have hinv := hden.inv₀ h1kG
  have hlim : ((1 : ℝ) / kG)⁻¹ = kG := by rw [one_div, inv_inv]
  unfold overallKG
  simpa [one_div, hlim] using hinv
end Engineering.Process.MassTransfer
