/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A continuous interval cutoff

The real cutoff used in endpoint-vanishing `L^p` approximation and Weyl's
equidistribution criterion. It takes values in `[0, 1]`, vanishes at the
endpoints, and has a plateau of height `1` for positive widths.
-/

namespace Real

/-- The clipped piecewise-linear cutoff, zero at `a` and `b`.
For `δ > 0`, it equals `1` on `[a + δ, b - δ]`; this plateau is nonempty
when `2 * δ ≤ b - a`. At `δ = 0`, the factor is identically zero. -/
noncomputable def intervalCutoff (a b δ x : ℝ) : ℝ :=
  max 0 (min 1 (min ((x - a) / δ) ((b - x) / δ)))

/-- The interval cutoff is nonnegative. -/
theorem intervalCutoff_nonneg (a b δ x : ℝ) : 0 ≤ intervalCutoff a b δ x :=
  le_max_left _ _

/-- The interval cutoff is at most `1`. -/
theorem intervalCutoff_le_one (a b δ x : ℝ) : intervalCutoff a b δ x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The interval cutoff is continuous, including at zero width. -/
theorem intervalCutoff_continuous (a b δ : ℝ) : Continuous (intervalCutoff a b δ) := by
  unfold intervalCutoff
  exact continuous_const.max (continuous_const.min
    ((continuous_id.sub continuous_const).div_const δ |>.min
      ((continuous_const.sub continuous_id).div_const δ)))

/-- The interval cutoff vanishes at the left endpoint for every width. -/
theorem intervalCutoff_eq_zero_left (a b δ : ℝ) : intervalCutoff a b δ a = 0 := by
  unfold intervalCutoff
  rw [sub_self, zero_div]
  exact max_eq_left (le_trans (min_le_right _ _) (min_le_left _ _))

/-- The interval cutoff vanishes at the right endpoint for every width. -/
theorem intervalCutoff_eq_zero_right (a b δ : ℝ) : intervalCutoff a b δ b = 0 := by
  unfold intervalCutoff
  rw [sub_self, zero_div]
  exact max_eq_left (le_trans (min_le_right _ _) (min_le_right _ _))

/-- At zero width, the interval cutoff is identically zero. -/
theorem intervalCutoff_zero_width (a b x : ℝ) : intervalCutoff a b 0 x = 0 := by
  simp [intervalCutoff]

/-- For positive width, the interval cutoff vanishes to the left of the interval. -/
theorem intervalCutoff_eq_zero_of_le (a b δ x : ℝ) (hδ : 0 < δ) (hx : x ≤ a) :
    intervalCutoff a b δ x = 0 := by
  unfold intervalCutoff
  have h1 : (x - a) / δ ≤ 0 := by
    rw [div_le_iff₀ hδ, zero_mul]
    exact sub_nonpos.mpr hx
  exact max_eq_left
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h1))

/-- For positive width, the interval cutoff vanishes to the right of the interval. -/
theorem intervalCutoff_eq_zero_of_ge (a b δ x : ℝ) (hδ : 0 < δ) (hx : b ≤ x) :
    intervalCutoff a b δ x = 0 := by
  unfold intervalCutoff
  have h1 : (b - x) / δ ≤ 0 := by
    rw [div_le_iff₀ hδ, zero_mul]
    exact sub_nonpos.mpr hx
  exact max_eq_left
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h1))

/-- For positive width, the interval cutoff equals `1` on its plateau. -/
theorem intervalCutoff_eq_one (a b δ x : ℝ) (hδ : 0 < δ)
    (hx1 : a + δ ≤ x) (hx2 : x ≤ b - δ) : intervalCutoff a b δ x = 1 := by
  have h1 : (1 : ℝ) ≤ (x - a) / δ := by
    rw [le_div_iff₀ hδ, one_mul]
    linarith
  have h2 : (1 : ℝ) ≤ (b - x) / δ := by
    rw [le_div_iff₀ hδ, one_mul]
    linarith
  have hmin : (1 : ℝ) ≤ min ((x - a) / δ) ((b - x) / δ) := le_min h1 h2
  unfold intervalCutoff
  rw [min_eq_left hmin, max_eq_right zero_le_one]

end Real
