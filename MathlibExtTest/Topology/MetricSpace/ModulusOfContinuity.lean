/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.MetricSpace.ModulusOfContinuity
import Mathlib.Tactic

namespace MetaMathlibExt

open scoped Topology

/-- The identity on `[0, 1]` is continuous, so its modulus of continuity
tends to `0` as the scale tends to `0⁺`. -/
example : Filter.Tendsto (modulusOfContinuity (fun x : ℝ => x) 0 1) (𝓝[>] 0) (𝓝 0) :=
  modulusOfContinuity_tendsto_zero _ 0 1 (by norm_num) continuous_id.continuousOn

/-- Nonnegativity of the modulus at a nonnegative scale, for a concrete
continuous function. -/
example : 0 ≤ modulusOfContinuity (fun x : ℝ => x) 0 1 (1 / 2) :=
  modulusOfContinuity_nonneg _ 0 1 (by norm_num) continuous_id.continuousOn (by norm_num)

/-- Monotonicity in the scale: enlarging the scale cannot shrink the modulus. -/
example : modulusOfContinuity (fun x : ℝ => x) 0 1 1 ≤ modulusOfContinuity (fun x : ℝ => x) 0 1 2 :=
  modulusOfContinuity_mono _ 0 1 (by norm_num) continuous_id.continuousOn (by norm_num)
    (by norm_num)

/-- The defining bound, applied: for `x, y ∈ [0, 1]` with `|x - y| ≤ 1 / 2`,
the identity's variation is bounded by its modulus at scale `1 / 2`. -/
example : |(0 : ℝ) - 1 / 2| ≤ modulusOfContinuity (fun x : ℝ => x) 0 1 (1 / 2) :=
  le_modulusOfContinuity _ 0 1 (1 / 2) continuous_id.continuousOn
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)

/-- A sharp value: the modulus of continuity of `x ↦ 2 * x` on `[0, 1]` at
scale `1 / 2` is exactly `1`: the upper bound comes from
`|2x - 2y| = 2|x - y| ≤ 1` on the defining set, and the lower bound from the
pair `x = 0, y = 1 / 2`. -/
example : modulusOfContinuity (fun x : ℝ => 2 * x) 0 1 (1 / 2) = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => 2 * x) (Set.Icc 0 1) :=
    (continuous_const.mul continuous_id).continuousOn
  apply le_antisymm
  · unfold modulusOfContinuity
    apply csSup_le _ _
    · exact ⟨|2 * (0 : ℝ) - 2 * 0|, (0 : ℝ), ⟨by norm_num, by norm_num⟩, (0 : ℝ),
        ⟨by norm_num, by norm_num⟩, by norm_num⟩
    · rintro d ⟨x, hx, y, hy, hxy, rfl⟩
      have h : |2 * x - 2 * y| = 2 * |x - y| := by
        rw [← mul_sub, abs_mul]
        norm_num
      rw [h]
      linarith
  · have h := le_modulusOfContinuity (fun x : ℝ => 2 * x) 0 1 (1 / 2) hcont
      (x := (0 : ℝ)) ⟨by norm_num, by norm_num⟩ (y := (1 / 2 : ℝ))
      ⟨by norm_num, by norm_num⟩ (by norm_num)
    norm_num at h
    exact h

end MetaMathlibExt
