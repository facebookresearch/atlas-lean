/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.Manning
import Mathlib.Tactic.Positivity

/-!
# Rectangular normal-depth uniqueness

## i. Overview

For a rectangular channel of width `b > 0` at depth `h > 0`, the
Manning discharge with positive combined prefactor `C`
(roughness and slope) is `C * (b * h) * ((b * h) / (b + 2 * h)) ^
(2 / 3)`, using flow area `b * h` and hydraulic radius
`(b * h) / (b + 2 * h)`. Both factors increase with depth, so the
discharge is strictly increasing in positive depth and a
prescribed discharge has at most one positive normal depth. No
existence or range claim is made.

## ii. Key results

- `EarthScience.rectangularDischarge_strictMonoOn`: strict
  increase in positive depth.
- `EarthScience.rectangular_normal_depth_unique`: at most one
  positive normal depth.
- `EarthScience.rectangularDischarge_eq_manningDischarge`: the
  rectangular specialization of the Manning discharge.

## iii. Table of contents

- A. Rectangular discharge and uniqueness

## iv. References

- V. T. Chow, *Open-Channel Hydraulics*, McGraw-Hill, 1959
  (normal depth in a rectangular channel).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Rectangular discharge and uniqueness -/

/-- Rectangular-channel Manning discharge at depth `h`, width `b`, and combined prefactor `C`
(roughness and slope), for all real inputs: `C * (b * h) * ((b * h) / (b + 2 * h)) ^ (2 / 3)`, using
area `b * h` and hydraulic radius `(b * h) / (b + 2 * h)`. With the conventions `x / 0 = 0` and
`0 ^ y = 0` for `y ≠ 0`, it is `0` when `b + 2 * h = 0`; a negative base `x` gives
`|x| ^ y * cos (π y)`. The intended domain is `C > 0`, `b > 0` and `h > 0`. -/
noncomputable def rectangularDischarge (C b h : ℝ) : ℝ :=
  C * (b * h) * ((b * h) / (b + 2 * h)) ^ ((2 : ℝ) / 3)

/-- Rectangular normal-depth monotonicity: for fixed positive
prefactor and width, discharge is strictly increasing in
positive depth. This is an at-most-one-depth statement; no
existence or range claim is made. -/
theorem rectangularDischarge_strictMonoOn {C b : ℝ}
    (hC : 0 < C) (hb : 0 < b) :
    StrictMonoOn (rectangularDischarge C b) (Set.Ioi 0) := by
  intro h1 hh1 h2 hh2 h12
  simp only [Set.mem_Ioi] at hh1 hh2
  have hA : b * h1 < b * h2 := mul_lt_mul_of_pos_left h12 hb
  have hD1 : (0 : ℝ) < b + 2 * h1 := by positivity
  have hD2 : (0 : ℝ) < b + 2 * h2 := by positivity
  have hR : (b * h1) / (b + 2 * h1) < (b * h2) / (b + 2 * h2) := by
    rw [div_lt_div_iff₀ hD1 hD2]
    nlinarith [mul_pos hb hb, h12, hh1, hh2]
  have hR1pos : (0 : ℝ) < (b * h1) / (b + 2 * h1) :=
    div_pos (mul_pos hb hh1) hD1
  have hrpow : ((b * h1) / (b + 2 * h1)) ^ ((2 : ℝ) / 3)
      < ((b * h2) / (b + 2 * h2)) ^ ((2 : ℝ) / 3) :=
    Real.rpow_lt_rpow hR1pos.le hR (by norm_num)
  have hrpow1pos : (0 : ℝ) < ((b * h1) / (b + 2 * h1)) ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hR1pos _
  have hu : C * (b * h1) < C * (b * h2) := mul_lt_mul_of_pos_left hA hC
  have hu2pos : (0 : ℝ) < C * (b * h2) := mul_pos hC (mul_pos hb hh2)
  show rectangularDischarge C b h1 < rectangularDischarge C b h2
  unfold rectangularDischarge
  exact (mul_lt_mul_of_pos_right hu hrpow1pos).trans
    (mul_lt_mul_of_pos_left hrpow hu2pos)

/-- For positive prefactor and width, a prescribed discharge has at
most one positive rectangular normal depth. -/
theorem rectangular_normal_depth_unique {C b h1 h2 : ℝ}
    (hC : 0 < C) (hb : 0 < b) (hh1 : 0 < h1) (hh2 : 0 < h2)
    (h : rectangularDischarge C b h1
      = rectangularDischarge C b h2) :
    h1 = h2 := by
  exact (rectangularDischarge_strictMonoOn hC hb).injOn
    (Set.mem_Ioi.mpr hh1) (Set.mem_Ioi.mpr hh2) h

/-- Bridge to the Manning discharge: for all real `n`, `S`, `b` and `h`, a rectangular discharge
with prefactor `sqrt S / n` is the Manning discharge at area `b * h` and hydraulic radius
`r = (b * h) / (b + 2 * h)`. With the conventions `sqrt x = 0` for `x < 0`, `x / 0 = 0` and
`x ^ y = |x| ^ y * cos (π y)` for `x < 0`, both sides are `0` when `S ≤ 0`, `n = 0` or
`b + 2 * h = 0`, and a negative `r` enters both sides as `r ^ (2 / 3) = -|r| ^ (2 / 3) / 2`. In
the hydraulic reading `n > 0` is the roughness coefficient, `S ≥ 0` the bed slope, and `b > 0`
and `h > 0` the channel width and flow depth, so that `r > 0`; the identity holds for all real
inputs. -/
theorem rectangularDischarge_eq_manningDischarge (n S b h : ℝ) :
    rectangularDischarge (Real.sqrt S / n) b h
      = manningDischarge n (b * h) ((b * h) / (b + 2 * h)) S := by
  unfold rectangularDischarge manningDischarge
  ring

end EarthScience
