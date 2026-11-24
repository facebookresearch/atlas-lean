/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.EulerBernoulliBeam

/-!
# Maximum deflection of the uniformly loaded beam

## i. Overview

The simply supported Euler--Bernoulli beam under uniform load `w`
(`Mechanics.EulerBernoulli.uniformLoadDeflection`, downward
positive) attains its maximum deflection on `[0, L]` at the
midpoint, with value `5 * w * L ^ 4 / (384 * EI)`, for `w ≥ 0`,
`EI > 0`, `L > 0`. At `w = 0` every point is a maximizer; the
midpoint value formula and the midpoint bound remain valid.

## ii. Key results

- `Mechanics.EulerBernoulli.uniformLoadDeflection_midpoint`:
  the midpoint value.
- `Mechanics.EulerBernoulli.uniformLoadDeflection_le_midpoint`:
  the midpoint bound on `[0, L]`.

## iii. Table of contents

- A. Midpoint value and maximum

## iv. References

- S. Timoshenko, *Strength of Materials, Part I*, 3rd edition, 1955
  (maximum deflection of a uniformly loaded simply supported beam).
-/

@[expose] public section

namespace Mechanics.EulerBernoulli

/-! ## A. Midpoint value and maximum -/

/-- Midpoint value of the uniform-load deflection: `5 * w * L ^ 4 / (384 * EI)`. With the convention
`x / 0 = 0` both sides are `0` when `EI = 0`. -/
theorem uniformLoadDeflection_midpoint (w EI L : ℝ) :
    uniformLoadDeflection w EI L (L / 2) = 5 * w * L ^ 4 / (384 * EI) := by
  unfold uniformLoadDeflection
  ring

/-- The midpoint maximizes the uniform-load deflection on
`[0, L]` for `w ≥ 0`, `EI > 0`, `L > 0`. -/
theorem uniformLoadDeflection_le_midpoint {w EI L x : ℝ} (hw : 0 ≤ w)
    (hEI : 0 < EI) (hL : 0 < L) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    uniformLoadDeflection w EI L x
      ≤ uniformLoadDeflection w EI L (L / 2) := by
  unfold uniformLoadDeflection
  have h_factor : (L ^ 3 * (L / 2) - 2 * L * (L / 2) ^ 3 + (L / 2) ^ 4)
      - (L ^ 3 * x - 2 * L * x ^ 3 + x ^ 4)
      = (x - L / 2) ^ 2 * (5 * L ^ 2 / 4 - x ^ 2 + L * x) := by ring
  have h_sq : 0 ≤ (x - L / 2) ^ 2 := sq_nonneg _
  have h_Lsubx : 0 ≤ L - x := sub_nonneg.mpr hxL
  have h_xLx : 0 ≤ x * (L - x) := mul_nonneg hx0 h_Lsubx
  have h_L2 : 0 ≤ 5 * L ^ 2 / 4 := by positivity
  have h_second_eq : 5 * L ^ 2 / 4 - x ^ 2 + L * x
      = 5 * L ^ 2 / 4 + x * (L - x) := by ring
  have h_second : 0 ≤ 5 * L ^ 2 / 4 - x ^ 2 + L * x := by
    rw [h_second_eq]
    exact add_nonneg h_L2 h_xLx
  have h_diff : 0 ≤ (L ^ 3 * (L / 2) - 2 * L * (L / 2) ^ 3 + (L / 2) ^ 4)
      - (L ^ 3 * x - 2 * L * x ^ 3 + x ^ 4) := by
    rw [h_factor]
    exact mul_nonneg h_sq h_second
  have hg : (L ^ 3 * x - 2 * L * x ^ 3 + x ^ 4)
      ≤ (L ^ 3 * (L / 2) - 2 * L * (L / 2) ^ 3 + (L / 2) ^ 4) :=
    sub_nonneg.mp h_diff
  have hwg : w * (L ^ 3 * x - 2 * L * x ^ 3 + x ^ 4)
      ≤ w * (L ^ 3 * (L / 2) - 2 * L * (L / 2) ^ 3 + (L / 2) ^ 4) :=
    mul_le_mul_of_nonneg_left hg hw
  have h_denom : 0 < 24 * EI := by positivity
  exact (div_le_div_iff_of_pos_right h_denom).mpr hwg

end Mechanics.EulerBernoulli
