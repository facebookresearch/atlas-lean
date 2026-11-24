/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.LinearPressurePanel

/-!
# Hydrostatic center of pressure

## i. Overview

For hydrostatic pressure with gradient `c = ρ * g > 0` on a panel
of width `w` over depths `[a, b]`, the center of pressure (moment
divided by force, from the shared linear-pressure panel) lies in
`[a, b]` for `c > 0`, `w > 0` and `0 ≤ a < b`, and for the
free-surface panel `[0, H]` with `H > 0` it is at depth `2 * H / 3`.

## ii. Key results

- `PhyslibExt.Mechanics.LinearPressurePanel.centerOfPressure_mem`:
  the center of pressure lies in the panel interval.
- `PhyslibExt.Mechanics.LinearPressurePanel.centerOfPressure_freeSurface`:
  the free-surface value `2 * H / 3`.

## iii. Table of contents

- A. Center of pressure

## iv. References

- Standard hydrostatic force theory on plane surfaces (center of
  pressure of a linear pressure distribution).
-/

@[expose] public section

namespace PhyslibExt.Mechanics.LinearPressurePanel

/-! ## A. Center of pressure -/

/-- The center of pressure lies in the panel interval `[a, b]` for `c > 0`, `w > 0` and `0 ≤ a < b`,
which make the force positive. -/
theorem centerOfPressure_mem {c w a b : ℝ} (hc : 0 < c) (hw : 0 < w)
    (hab : a < b) (ha : 0 ≤ a) :
    linearPressureMoment c w a b / linearPressureForce c w a b
      ∈ Set.Icc a b := by
  rw [linearPressureForce_eq, linearPressureMoment_eq]
  have hwc : 0 < w * c := mul_pos hw hc
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have h2 : a ^ 2 < b ^ 2 := pow_lt_pow_left₀ hab ha (by norm_num)
  have hd : 0 < b ^ 2 - a ^ 2 := sub_pos.mpr h2
  have hF : 0 < w * c * (b ^ 2 - a ^ 2) / 2 := by positivity
  rw [Set.mem_Icc, le_div_iff₀ hF, div_le_iff₀ hF]
  constructor
  · have h1 : 0 ≤ (b - a) ^ 2 * (2 * b + a) := by
      apply mul_nonneg (sq_nonneg _)
      linarith
    have heq : w * c * (b ^ 3 - a ^ 3) / 3 - a * (w * c * (b ^ 2 - a ^ 2) / 2)
        = w * c * ((b - a) ^ 2 * (2 * b + a) / 6) := by ring
    have hnn : 0 ≤ w * c * ((b - a) ^ 2 * (2 * b + a) / 6) :=
      mul_nonneg hwc.le (by linarith)
    linarith
  · have h1 : 0 ≤ (b - a) ^ 2 * (b + 2 * a) := by
      apply mul_nonneg (sq_nonneg _)
      linarith
    have heq : b * (w * c * (b ^ 2 - a ^ 2) / 2) - w * c * (b ^ 3 - a ^ 3) / 3
        = w * c * ((b - a) ^ 2 * (b + 2 * a) / 6) := by ring
    have hnn : 0 ≤ w * c * ((b - a) ^ 2 * (b + 2 * a) / 6) :=
      mul_nonneg hwc.le (by linarith)
    linarith

/-- Free-surface panel: center of pressure at depth `2 * H / 3`. -/
theorem centerOfPressure_freeSurface {c w H : ℝ} (hc : 0 < c)
    (hw : 0 < w) (hH : 0 < H) :
    linearPressureMoment c w 0 H / linearPressureForce c w 0 H
      = 2 * H / 3 := by
  rw [linearPressureForce_eq, linearPressureMoment_eq]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  have hF : 0 < w * c * H ^ 2 / 2 := by positivity
  have hFne : w * c * H ^ 2 / 2 ≠ 0 := ne_of_gt hF
  field_simp

end PhyslibExt.Mechanics.LinearPressurePanel
