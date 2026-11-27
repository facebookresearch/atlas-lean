/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Continuous radial clipping to the closed unit ball

For a normed real vector space E, put clip(x) = x/max(1,‖x‖).
This map is continuous, has norm at most one, and fixes every x with ‖x‖ ≤ 1.
For a target w in the closed unit ball and any z : E,
‖w - clip(z)‖ ≤ 2‖w-z‖.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a normed real vector space E, radialClip(x) =
(max(1,‖x‖))⁻¹ • x. The denominator is positive for every x. -/
noncomputable def radialClip (x : E) : E :=
  (max 1 ‖x‖)⁻¹ • x

/-- For every normed real vector space E, radialClip : E → E is continuous. -/
theorem continuous_radialClip : Continuous (radialClip : E → E) := by
  have hden : Continuous fun x : E ↦ max 1 ‖x‖ :=
    continuous_const.max continuous_norm
  have hne : ∀ x : E, max 1 ‖x‖ ≠ 0 := fun x ↦
    ne_of_gt (zero_lt_one.trans_le (le_max_left 1 ‖x‖))
  exact (hden.inv₀ hne).smul continuous_id

/-- For a normed real vector space E and x : E, ‖radialClip x‖ ≤ 1. -/
theorem norm_radialClip_le_one (x : E) : ‖radialClip x‖ ≤ 1 := by
  by_cases hx : ‖x‖ ≤ 1
  · simpa [radialClip, max_eq_left hx] using hx
  · have hx' : 1 < ‖x‖ := lt_of_not_ge hx
    have hpos : 0 < ‖x‖⁻¹ := inv_pos.mpr (zero_lt_one.trans hx')
    rw [radialClip, max_eq_right hx'.le, norm_smul, Real.norm_eq_abs,
      abs_of_pos hpos, inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans hx'))]

/-- For a normed real vector space E and x : E with ‖x‖ ≤ 1,
radialClip x = x. -/
theorem radialClip_eq_self {x : E} (hx : ‖x‖ ≤ 1) : radialClip x = x := by
  simp [radialClip, max_eq_left hx]

/-- For a normed real vector space E, w,z : E and ‖w‖ ≤ 1,
‖w - radialClip z‖ ≤ 2‖w-z‖. -/
theorem norm_sub_radialClip_le_two_mul (w z : E) (hw : ‖w‖ ≤ 1) :
    ‖w - radialClip z‖ ≤ 2 * ‖w - z‖ := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [radialClip_eq_self hz]
    nlinarith [norm_nonneg (w - z)]
  · have hz' : 1 < ‖z‖ := lt_of_not_ge hz
    have hznorm : 0 < ‖z‖ := zero_lt_one.trans hz'
    have hinvle : ‖z‖⁻¹ ≤ 1 := (inv_le_one₀ hznorm).2 hz'.le
    have hclip : ‖z - radialClip z‖ = ‖z‖ - 1 := by
      calc
        ‖z - radialClip z‖ = ‖(1 - ‖z‖⁻¹) • z‖ := by
          congr 1
          rw [radialClip, max_eq_right hz'.le]
          symm
          rw [sub_smul, one_smul]
        _ = |1 - ‖z‖⁻¹| * ‖z‖ := norm_smul _ _
        _ = (1 - ‖z‖⁻¹) * ‖z‖ := by
          rw [abs_of_nonneg (sub_nonneg.mpr hinvle)]
        _ = ‖z‖ - 1 := by
          field_simp
    have hzw : ‖z‖ - 1 ≤ ‖z - w‖ := by
      calc
        ‖z‖ - 1 ≤ ‖z‖ - ‖w‖ := sub_le_sub_left hw ‖z‖
        _ ≤ |‖z‖ - ‖w‖| := le_abs_self _
        _ ≤ ‖z - w‖ := abs_norm_sub_norm_le z w
    calc
      ‖w - radialClip z‖ = ‖(w - z) + (z - radialClip z)‖ := by
        congr 1
        abel
      _ ≤ ‖w - z‖ + ‖z - radialClip z‖ := norm_add_le _ _
      _ ≤ ‖w - z‖ + ‖z - w‖ := add_le_add_right (hclip.trans_le hzw) _
      _ = 2 * ‖w - z‖ := by rw [norm_sub_rev]; ring

end MathlibExt.Analysis.Normed.Module
