/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.OpenChannelSpecificEnergy
public import PhyslibExt.EarthScience.RectangularNormalDepth
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Sign.Basic

/-!
# Gradually varied flow in a rectangular channel

Away from the critical depth, the declared gradually-varied-flow slope has
sign `sign (y - yn) * sign (y - yc)`, where `yn` is a normal depth and
`yc` is the critical depth.

## i. Overview

Steady flow in a prismatic rectangular channel of width `b > 0`, distance
`x` positive downstream, depth `y > 0`, constant total discharge `Q` with
discharge per unit width `q = Q / b`, gravity `g > 0`, energy coefficient
`α = 1`, downhill bed slope `S0 > 0`, and Manning roughness `n > 0` in the
factor-1 SI form (`[n] = T * L^(-1/3)`; not the US-customary 1.49 form).
The model is declared, not derived: the equation is
`dy/dx = (S0 - Sf y) / (1 - q ^ 2 / (g * y ^ 3))`.

Flow area is `b * y` and hydraulic radius is `(b * y) / (b + 2 * y)`. The
friction slope `frictionSlope n b Q y` is Manning's law solved for slope at
depth `y`. The critical depth is `rectangularCriticalDepth q g = (q ^ 2 / g) ^ (1 / 3)`,
the minimizer exhibited by `specific_energy_unique_minimum`. A normal
depth `yn` is supplied as a positive depth whose rectangular Manning
discharge at bed slope `S0` equals `Q`; its existence is not claimed. The
channel is mild when `yc < yn` and steep when `yn < yc`.

Division by the flow area and hydraulic-radius power is physical only for
`b > 0`, `y > 0`; real powers are read on positive bases; `Real.sqrt S0`
is read for `S0 > 0`. The slope denominator vanishes exactly at `y = yc`,
where Lean's totalized division would give `0`; every result that reads
the slope as a derivative excludes `y = yc`. No ODE existence or profile
through `y = yc`, no hydraulic-jump location, no normal-depth existence,
no horizontal or adverse bed, no nonrectangular section, and no `α ≠ 1`.

## ii. Key results

- `EarthScience.frictionSlope` and `EarthScience.gvfSlope`: the friction
  slope and declared slope, using the critical depth
  `EarthScience.rectangularCriticalDepth`.
- `EarthScience.manningDischarge_frictionSlope` and
  `EarthScience.frictionSlope_eq_rectangularDischarge`: the Manning
  inversion and rectangular-discharge bridge.
- `EarthScience.sign_gvfSlope`: the sign certificate
  `sign (y - yn) * sign (y - yc)`.
- `EarthScience.gvfSlope_normalDepth`, `EarthScience.gvfSlope_mild`, and
  `EarthScience.gvfSlope_steep`: uniform flow and the three-zone signs.
- `EarthScience.sign_deriv_of_gvf`: the derivative reading for a profile
  satisfying the declared equation at one point.

## iii. Table of contents

- A. Friction slope, critical depth, and the declared slope
- B. Sign certificate and profile regimes

## iv. References

- V. T. Chow, *Open-Channel Hydraulics*, McGraw-Hill, 1959, Ch. 9,
  Art. 9-2, pp. 218-221, Eqs. (9-3), (9-4), (9-12), (9-13). Chow's
  Manning Eq. (9-8) is the US form; this module uses the SI factor-1 form.
- `EarthScience.manningDischarge` and
  `EarthScience.rectangularDischarge_strictMonoOn`.

## A. Friction slope, critical depth, and the declared slope
-/

@[expose] public section

namespace EarthScience

/-- Friction slope of a rectangular channel of width `b` carrying
total discharge `Q` at depth `y` under Manning roughness `n`:
Manning's law solved for slope,
`(n * Q / (A * R ^ (2 / 3))) ^ 2` with `A = b * y` and
`R = (b * y) / (b + 2 * y)`. Physical for `0 < n`, `0 < b`,
`0 < y`, `0 ≤ Q`; the division is totalized elsewhere: with the
conventions `a / 0 = 0` and `0 ^ r = 0` for `r ≠ 0`, it is `0` when
`b * y = 0` or `b + 2 * y = 0`; with `a ^ r = |a| ^ r * cos (π r)` for
`a < 0`, a negative hydraulic radius enters as `-|R| ^ (2 / 3) / 2`. -/
noncomputable def frictionSlope (n b Q y : ℝ) : ℝ :=
  (n * Q / ((b * y) * ((b * y) / (b + 2 * y)) ^ ((2 : ℝ) / 3))) ^ 2

/-- Right-hand side of the declared steady gradually-varied-flow
equation in a rectangular channel (Chow 1959, `α = 1`):
`(S0 - Sf y) / (1 - (Q / b) ^ 2 / (g * y ^ 3))`. Physical for
`0 < b`, `0 < n`, `0 < S0`, `0 < g`, `0 < y`, `y ≠ yc`; at a
positive critical depth `y = yc` (with `b, g > 0`) the totalized
division returns `0`, which is not a physical slope. With the convention `a / 0 = 0`, the term
`(Q / b) ^ 2 / (g * y ^ 3)` is `0` when `b = 0`, `g = 0` or `y = 0`. Inside `Sf`, a negative
hydraulic radius `R = (b * y) / (b + 2 * y)` enters as `R ^ (2 / 3) = -|R| ^ (2 / 3) / 2`, by the
convention `a ^ r = |a| ^ r * cos (π r)` for `a < 0`. -/
noncomputable def gvfSlope (n S0 b Q g y : ℝ) : ℝ :=
  (S0 - frictionSlope n b Q y) / (1 - (Q / b) ^ 2 / (g * y ^ 3))

private lemma rectDischarge_pos {C b h : ℝ} (hC : 0 < C) (hb : 0 < b)
    (hh : 0 < h) : 0 < rectangularDischarge C b h := by
  unfold rectangularDischarge
  apply mul_pos (mul_pos hC (mul_pos hb hh))
  apply Real.rpow_pos_of_pos
  apply div_pos (mul_pos hb hh)
  linarith

private lemma discharge_pos_of_normal {n S0 b Q yn : ℝ} (hb : 0 < b)
    (hn : 0 < n) (hS0 : 0 < S0) (hyn0 : 0 < yn)
    (hyn : rectangularDischarge (Real.sqrt S0 / n) b yn = Q) : 0 < Q := by
  rw [← hyn]
  apply rectDischarge_pos _ hb hyn0
  exact div_pos (Real.sqrt_pos.mpr hS0) hn

private lemma sign_inv {a : ℝ} (ha : a ≠ 0) :
    SignType.sign a⁻¹ = SignType.sign a := by
  rcases lt_trichotomy a 0 with h | h | h
  · rw [sign_neg h, sign_neg (inv_neg''.mpr h)]
  · exact absurd h ha
  · rw [sign_pos h, sign_pos (inv_pos.mpr h)]

private lemma sign_div {a b : ℝ} (hb : b ≠ 0) :
    SignType.sign (a / b) = SignType.sign a * SignType.sign b := by
  rw [div_eq_mul_inv, sign_mul, sign_inv hb]

/-- Manning inversion: on the physical domain, Manning's discharge at
area `b * y`, hydraulic radius `(b * y) / (b + 2 * y)` and slope
`frictionSlope n b Q y` is exactly `Q`. This is the defining reading
of the friction slope. -/
lemma manningDischarge_frictionSlope {n b Q y : ℝ} (hn : 0 < n)
    (hb : 0 < b) (hy : 0 < y) (hQ : 0 ≤ Q) :
    manningDischarge n (b * y) ((b * y) / (b + 2 * y))
      (frictionSlope n b Q y) = Q := by
  unfold manningDischarge frictionSlope
  have hA : 0 < b * y := mul_pos hb hy
  have hden : 0 < b + 2 * y := by linarith
  have hR : 0 < (b * y) / (b + 2 * y) := div_pos hA hden
  have hRp : 0 < ((b * y) / (b + 2 * y)) ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hR _
  have hD : 0 < (b * y) * ((b * y) / (b + 2 * y)) ^ ((2 : ℝ) / 3) :=
    mul_pos hA hRp
  have hfrac :
      0 ≤ n * Q / ((b * y) * ((b * y) / (b + 2 * y)) ^ ((2 : ℝ) / 3)) :=
    div_nonneg (mul_nonneg (le_of_lt hn) hQ) (le_of_lt hD)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hfrac]
  have hn' : n ≠ 0 := ne_of_gt hn
  have hD' : (b * y) * ((b * y) / (b + 2 * y)) ^ ((2 : ℝ) / 3) ≠ 0 :=
    ne_of_gt hD
  field_simp

/-- Bridge to the rectangular discharge: for a downhill bed
`0 < S0`, the friction slope equals
`S0 * (Q / rectangularDischarge (sqrt S0 / n) b y) ^ 2`, the bed slope
scaled by the squared ratio of the carried discharge to the uniform-flow discharge at depth `y`. It
also holds where a denominator vanishes, with the convention `x / 0 = 0` (both sides are `0` when
`n = 0`), and for a negative hydraulic radius `R = (b * y) / (b + 2 * y)`, which enters both sides
as `R ^ (2 / 3) = -|R| ^ (2 / 3) / 2` by the convention `x ^ r = |x| ^ r * cos (π r)` for
`x < 0`. -/
lemma frictionSlope_eq_rectangularDischarge {n S0 b Q y : ℝ}
    (hS0 : 0 < S0) :
    frictionSlope n b Q y
      = S0 * (Q / rectangularDischarge (Real.sqrt S0 / n) b y) ^ 2 := by
  unfold frictionSlope rectangularDischarge
  have hs0 : Real.sqrt S0 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hS0)
  have hS0' : S0 ≠ 0 := ne_of_gt hS0
  have hsq : (Real.sqrt S0) ^ 2 = S0 := Real.sq_sqrt (le_of_lt hS0)
  have hassoc : ((Real.sqrt S0 / n) * (b * y))
        * ((b * y) / (b + 2 * y)) ^ ((2 : ℝ) / 3)
      = (Real.sqrt S0 / n)
        * ((b * y) * ((b * y) / (b + 2 * y)) ^ ((2 : ℝ) / 3)) :=
    mul_assoc _ _ _
  rw [hassoc]
  set D : ℝ := (b * y) * ((b * y) / (b + 2 * y)) ^ ((2 : ℝ) / 3)
    with hDdef
  by_cases hD : D = 0
  · rw [hD, div_zero, mul_zero, div_zero, zero_pow two_ne_zero, mul_zero]
  · by_cases hn0 : n = 0
    · rw [hn0, zero_mul, zero_div, div_zero, zero_mul, div_zero,
        zero_pow two_ne_zero, mul_zero]
    · have hn0' : n ≠ 0 := hn0
      have hnsD : (Real.sqrt S0 / n) * D ≠ 0 :=
        mul_ne_zero (div_ne_zero hs0 hn0') hD
      have hsD : Real.sqrt S0 * D ≠ 0 := mul_ne_zero hs0 hD
      have e1 : Q / ((Real.sqrt S0 / n) * D)
          = (Q * n) / (Real.sqrt S0 * D) := by
        field_simp
      rw [e1, div_pow, div_pow]
      have h2 : (Real.sqrt S0 * D) ^ 2 = S0 * D ^ 2 := by
        rw [mul_pow, hsq]
      rw [h2]
      have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
      have hSD2 : S0 * D ^ 2 ≠ 0 := mul_ne_zero hS0' hD2
      field_simp

/-! ## B. Sign certificate and profile regimes -/

/-- Sign certificate for the gradually-varied-flow slope: for a positive normal depth `yn`
(rectangular Manning discharge `Q` at bed slope `S0`) and a depth `y > 0` away from the critical
depth `yc = rectangularCriticalDepth (Q / b) g`, the declared slope has sign
`sign (y - yn) * sign (y - yc)`. Positive flow `0 < Q` follows from `hyn` and is not a separate
premise. The premise `y ≠ yc` keeps the totalized value at the singular point out of the claim. Here
the channel width `b`, the roughness `n`, the bed slope `S0` and `g` are positive, and `yn > 0` is a
normal depth for `Q`: `(√S0 / n) * (b * yn) * ((b * yn) / (b + 2 * yn)) ^ (2 / 3) = Q`, with
`yc = ((Q / b) ^ 2 / g) ^ (1 / 3)` the critical depth. -/
theorem sign_gvfSlope {n S0 b Q g yn y : ℝ} (hb : 0 < b) (hn : 0 < n)
    (hS0 : 0 < S0) (hg : 0 < g) (hyn0 : 0 < yn)
    (hyn : rectangularDischarge (Real.sqrt S0 / n) b yn = Q)
    (hy : 0 < y) (hyc : y ≠ rectangularCriticalDepth (Q / b) g) :
    SignType.sign (gvfSlope n S0 b Q g y)
      = SignType.sign (y - yn)
        * SignType.sign (y - rectangularCriticalDepth (Q / b) g) := by
  have hmono : StrictMonoOn (rectangularDischarge (Real.sqrt S0 / n) b)
      (Set.Ioi 0) :=
    rectangularDischarge_strictMonoOn (div_pos (Real.sqrt_pos.mpr hS0) hn) hb
  have hQ : 0 < Q := discharge_pos_of_normal hb hn hS0 hyn0 hyn
  have hC : 0 < Real.sqrt S0 / n := div_pos (Real.sqrt_pos.mpr hS0) hn
  have hRy : 0 < rectangularDischarge (Real.sqrt S0 / n) b y :=
    rectDischarge_pos hC hb hy
  have hRy' : rectangularDischarge (Real.sqrt S0 / n) b y ≠ 0 :=
    ne_of_gt hRy
  have hSf : frictionSlope n b Q y
      = S0 * (Q / rectangularDischarge (Real.sqrt S0 / n) b y) ^ 2 :=
    frictionSlope_eq_rectangularDischarge hS0
  have hb' : b ≠ 0 := ne_of_gt hb
  have hg' : g ≠ 0 := ne_of_gt hg
  have hy3 : y ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hy)
  have hgy3 : g * y ^ 3 ≠ 0 := mul_ne_zero hg' hy3
  have hyc3 : (rectangularCriticalDepth (Q / b) g) ^ 3 = (Q / b) ^ 2 / g :=
    rectangularCriticalDepth_cube hg
  have hfac : y ^ 3 - (rectangularCriticalDepth (Q / b) g) ^ 3
      = (y - rectangularCriticalDepth (Q / b) g)
        * (y ^ 2 + y * rectangularCriticalDepth (Q / b) g
          + (rectangularCriticalDepth (Q / b) g) ^ 2) := by
    ring
  have hpos2 : 0 < y ^ 2 + y * rectangularCriticalDepth (Q / b) g
      + (rectangularCriticalDepth (Q / b) g) ^ 2 := by
    have h1 : 0 < y ^ 2 := by positivity
    have h2 : 0 ≤ y * rectangularCriticalDepth (Q / b) g :=
      mul_nonneg (le_of_lt hy) (rectangularCriticalDepth_nonneg hg)
    have h3 : 0 ≤ (rectangularCriticalDepth (Q / b) g) ^ 2 := sq_nonneg _
    linarith
  have hden_eq : (1 - (Q / b) ^ 2 / (g * y ^ 3))
      = (y ^ 3 - (rectangularCriticalDepth (Q / b) g) ^ 3) / y ^ 3 := by
    rw [hyc3]
    field_simp
  have hden_ne : (1 - (Q / b) ^ 2 / (g * y ^ 3)) ≠ 0 := by
    rw [hden_eq]
    apply div_ne_zero _ hy3
    rw [hfac]
    intro hcon
    rcases mul_eq_zero.mp hcon with h | h
    · exact hyc (sub_eq_zero.mp h)
    · exact absurd h (ne_of_gt hpos2)
  have hsign_num : SignType.sign (S0 - frictionSlope n b Q y)
      = SignType.sign (y - yn) := by
    have hfactor : S0 - frictionSlope n b Q y
        = S0 * (1 - (Q / rectangularDischarge (Real.sqrt S0 / n) b y) ^ 2) := by
      rw [hSf]
      ring
    rw [hfactor, sign_mul, sign_pos hS0, one_mul]
    have ht : 0 < Q / rectangularDischarge (Real.sqrt S0 / n) b y :=
      div_pos hQ hRy
    have hfac2 : (1 - (Q / rectangularDischarge (Real.sqrt S0 / n) b y) ^ 2)
        = (1 - Q / rectangularDischarge (Real.sqrt S0 / n) b y)
          * (1 + Q / rectangularDischarge (Real.sqrt S0 / n) b y) := by
      ring
    rw [hfac2, sign_mul, sign_pos (by linarith : 0 < 1
      + Q / rectangularDischarge (Real.sqrt S0 / n) b y), mul_one]
    have h1t : (1 - Q / rectangularDischarge (Real.sqrt S0 / n) b y)
        = (rectangularDischarge (Real.sqrt S0 / n) b y - Q)
          / rectangularDischarge (Real.sqrt S0 / n) b y := by
      field_simp
    rw [h1t, sign_div hRy', sign_pos hRy, mul_one, ← hyn]
    rcases lt_trichotomy y yn with h | h | h
    · have hlt : rectangularDischarge (Real.sqrt S0 / n) b y
          < rectangularDischarge (Real.sqrt S0 / n) b yn :=
        (hmono.lt_iff_lt (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hyn0)).mpr h
      rw [sign_neg (sub_neg.mpr hlt), sign_neg (sub_neg.mpr h)]
    · rw [h, sub_self, sub_self]
    · have hgt : rectangularDischarge (Real.sqrt S0 / n) b yn
          < rectangularDischarge (Real.sqrt S0 / n) b y :=
        (hmono.lt_iff_lt (Set.mem_Ioi.mpr hyn0) (Set.mem_Ioi.mpr hy)).mpr h
      rw [sign_pos (sub_pos.mpr hgt), sign_pos (sub_pos.mpr h)]
  have hsign_den : SignType.sign (1 - (Q / b) ^ 2 / (g * y ^ 3))
      = SignType.sign (y - rectangularCriticalDepth (Q / b) g) := by
    rw [hden_eq, sign_div hy3, sign_pos (pow_pos hy 3), mul_one, hfac,
      sign_mul, sign_pos hpos2, mul_one]
  unfold gvfSlope
  rw [sign_div hden_ne, hsign_num, hsign_den]

/-- At the normal depth the declared slope vanishes: uniform flow is a constant-depth solution of
the equation, read only when `yn ≠ yc` (at `yn = yc` the slope is the singular `0 / 0`). Here the
channel width `b`, the roughness `n`, the bed slope `S0` and `g` are positive, and `yn > 0` is a
normal depth for `Q`: `(√S0 / n) * (b * yn) * ((b * yn) / (b + 2 * yn)) ^ (2 / 3) = Q`, with
`yc = ((Q / b) ^ 2 / g) ^ (1 / 3)` the critical depth. -/
theorem gvfSlope_normalDepth {n S0 b Q g yn : ℝ} (hb : 0 < b)
    (hn : 0 < n) (hS0 : 0 < S0) (_hg : 0 < g) (hyn0 : 0 < yn)
    (hyn : rectangularDischarge (Real.sqrt S0 / n) b yn = Q)
    (_hne : yn ≠ rectangularCriticalDepth (Q / b) g) :
    gvfSlope n S0 b Q g yn = 0 := by
  have hQ : 0 < Q := discharge_pos_of_normal hb hn hS0 hyn0 hyn
  have hSf : frictionSlope n b Q yn = S0 := by
    have h : frictionSlope n b Q yn
        = S0 * (Q / rectangularDischarge (Real.sqrt S0 / n) b yn) ^ 2 :=
      frictionSlope_eq_rectangularDischarge hS0
    rw [hyn, div_self (ne_of_gt hQ)] at h
    simpa using h
  unfold gvfSlope
  rw [hSf, sub_self, zero_div]

/-- Mild channel (`yc < yn`): the depth rises downstream above the normal depth (zone 1), falls
between critical and normal depth (zone 2), and rises below critical depth (zone 3). Here the
channel width `b`, the roughness `n`, the bed slope `S0` and `g` are positive, and `yn > 0` is a
normal depth for `Q`: `(√S0 / n) * (b * yn) * ((b * yn) / (b + 2 * yn)) ^ (2 / 3) = Q`, with
`yc = ((Q / b) ^ 2 / g) ^ (1 / 3)` the critical depth. -/
theorem gvfSlope_mild {n S0 b Q g yn : ℝ} (hb : 0 < b) (hn : 0 < n)
    (hS0 : 0 < S0) (hg : 0 < g) (hyn0 : 0 < yn)
    (hyn : rectangularDischarge (Real.sqrt S0 / n) b yn = Q)
    (hmild : rectangularCriticalDepth (Q / b) g < yn) :
    (∀ y, yn < y → 0 < gvfSlope n S0 b Q g y) ∧
    (∀ y, rectangularCriticalDepth (Q / b) g < y → y < yn →
      gvfSlope n S0 b Q g y < 0) ∧
    (∀ y, 0 < y → y < rectangularCriticalDepth (Q / b) g →
      0 < gvfSlope n S0 b Q g y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy_gt
    have hy0 : 0 < y := lt_trans hyn0 hy_gt
    have hne : y ≠ rectangularCriticalDepth (Q / b) g :=
      ne_of_gt (lt_trans hmild hy_gt)
    have h := sign_gvfSlope hb hn hS0 hg hyn0 hyn hy0 hne
    have e1 : SignType.sign (y - yn) = 1 := sign_pos (sub_pos.mpr hy_gt)
    have e2 : SignType.sign (y - rectangularCriticalDepth (Q / b) g) = 1 :=
      sign_pos (sub_pos.mpr (lt_trans hmild hy_gt))
    rw [e1, e2, mul_one] at h
    exact sign_eq_one_iff.mp h
  · intro y h1 h2
    have hy0 : 0 < y := lt_of_le_of_lt (rectangularCriticalDepth_nonneg hg) h1
    have hne : y ≠ rectangularCriticalDepth (Q / b) g := ne_of_gt h1
    have h := sign_gvfSlope hb hn hS0 hg hyn0 hyn hy0 hne
    have e1 : SignType.sign (y - yn) = -1 := sign_neg (sub_neg.mpr h2)
    have e2 : SignType.sign (y - rectangularCriticalDepth (Q / b) g) = 1 :=
      sign_pos (sub_pos.mpr h1)
    rw [e1, e2, mul_one] at h
    exact sign_eq_neg_one_iff.mp h
  · intro y hy0 hlt
    have hne : y ≠ rectangularCriticalDepth (Q / b) g := ne_of_lt hlt
    have h := sign_gvfSlope hb hn hS0 hg hyn0 hyn hy0 hne
    have e1 : SignType.sign (y - yn) = -1 :=
      sign_neg (sub_neg.mpr (lt_trans hlt hmild))
    have e2 : SignType.sign (y - rectangularCriticalDepth (Q / b) g) = -1 :=
      sign_neg (sub_neg.mpr hlt)
    rw [e1, e2] at h
    have h9 : (-1 : SignType) * (-1) = 1 := by simp
    rw [h9] at h
    exact sign_eq_one_iff.mp h

/-- Steep channel (`yn < yc`): the depth rises downstream above the critical depth (zone 1), falls
between normal and critical depth (zone 2), and rises below normal depth (zone 3). Here the channel
width `b`, the roughness `n`, the bed slope `S0` and `g` are positive, and `yn > 0` is a normal
depth for `Q`: `(√S0 / n) * (b * yn) * ((b * yn) / (b + 2 * yn)) ^ (2 / 3) = Q`, with
`yc = ((Q / b) ^ 2 / g) ^ (1 / 3)` the critical depth. -/
theorem gvfSlope_steep {n S0 b Q g yn : ℝ} (hb : 0 < b) (hn : 0 < n)
    (hS0 : 0 < S0) (hg : 0 < g) (hyn0 : 0 < yn)
    (hyn : rectangularDischarge (Real.sqrt S0 / n) b yn = Q)
    (hsteep : yn < rectangularCriticalDepth (Q / b) g) :
    (∀ y, rectangularCriticalDepth (Q / b) g < y → 0 < gvfSlope n S0 b Q g y) ∧
    (∀ y, yn < y → y < rectangularCriticalDepth (Q / b) g →
      gvfSlope n S0 b Q g y < 0) ∧
    (∀ y, 0 < y → y < yn → 0 < gvfSlope n S0 b Q g y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy_gt
    have hy0 : 0 < y := lt_of_le_of_lt (rectangularCriticalDepth_nonneg hg) hy_gt
    have hne : y ≠ rectangularCriticalDepth (Q / b) g := ne_of_gt hy_gt
    have h := sign_gvfSlope hb hn hS0 hg hyn0 hyn hy0 hne
    have e1 : SignType.sign (y - yn) = 1 :=
      sign_pos (sub_pos.mpr (lt_trans hsteep hy_gt))
    have e2 : SignType.sign (y - rectangularCriticalDepth (Q / b) g) = 1 :=
      sign_pos (sub_pos.mpr hy_gt)
    rw [e1, e2, mul_one] at h
    exact sign_eq_one_iff.mp h
  · intro y h1 h2
    have hy0 : 0 < y := lt_trans hyn0 h1
    have hne : y ≠ rectangularCriticalDepth (Q / b) g := ne_of_lt h2
    have h := sign_gvfSlope hb hn hS0 hg hyn0 hyn hy0 hne
    have e1 : SignType.sign (y - yn) = 1 := sign_pos (sub_pos.mpr h1)
    have e2 : SignType.sign (y - rectangularCriticalDepth (Q / b) g) = -1 :=
      sign_neg (sub_neg.mpr h2)
    rw [e1, e2, one_mul] at h
    exact sign_eq_neg_one_iff.mp h
  · intro y hy0 hlt
    have hne : y ≠ rectangularCriticalDepth (Q / b) g :=
      ne_of_lt (lt_trans hlt hsteep)
    have h := sign_gvfSlope hb hn hS0 hg hyn0 hyn hy0 hne
    have e1 : SignType.sign (y - yn) = -1 := sign_neg (sub_neg.mpr hlt)
    have e2 : SignType.sign (y - rectangularCriticalDepth (Q / b) g) = -1 :=
      sign_neg (sub_neg.mpr (lt_trans hlt hsteep))
    rw [e1, e2] at h
    have h9 : (-1 : SignType) * (-1) = 1 := by simp
    rw [h9] at h
    exact sign_eq_one_iff.mp h

/-- Derivative reading: if a depth profile `Y` (distance `x` positive downstream) satisfies the
declared gradually-varied-flow equation at `x`, with `0 < Y x` and `Y x ≠ yc`, then the sign of
`dY/dx` at `x` is `sign (Y x - yn) * sign (Y x - yc)`. No profile existence is claimed. Here the
channel width `b`, the roughness `n`, the bed slope `S0` and `g` are positive, and `yn > 0` is a
normal depth for `Q`: `(√S0 / n) * (b * yn) * ((b * yn) / (b + 2 * yn)) ^ (2 / 3) = Q`, with
`yc = ((Q / b) ^ 2 / g) ^ (1 / 3)` the critical depth. -/
theorem sign_deriv_of_gvf {n S0 b Q g yn : ℝ} {Y : ℝ → ℝ} {x : ℝ}
    (hb : 0 < b) (hn : 0 < n) (hS0 : 0 < S0) (hg : 0 < g)
    (hyn0 : 0 < yn)
    (hyn : rectangularDischarge (Real.sqrt S0 / n) b yn = Q)
    (hY : HasDerivAt Y (gvfSlope n S0 b Q g (Y x)) x) (hy : 0 < Y x)
    (hyc : Y x ≠ rectangularCriticalDepth (Q / b) g) :
    SignType.sign (deriv Y x)
      = SignType.sign (Y x - yn)
        * SignType.sign (Y x - rectangularCriticalDepth (Q / b) g) := by
  have hder : deriv Y x = gvfSlope n S0 b Q g (Y x) := hY.deriv
  rw [hder]
  exact sign_gvfSlope hb hn hS0 hg hyn0 hyn hy hyc

end EarthScience
