/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.MeanRecurrenceTime

/-!
# Checks for the geometric-series identities behind the return period

Concrete instances of `PhyslibExt.EarthScience.MeanRecurrenceTime`: the
weighted series is `2` at `p = 1 / 2`, `100` at `p = 0.01` and `1` at the
boundary `p = 1`, and the geometric series is `4` at `p = 1 / 4`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete values
- B. Boundary

## iv. References

- `PhyslibExt.EarthScience.MeanRecurrenceTime`
-/

/-- `p = 1 / 2`: the weighted series is `2`. -/
example :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((0.5 : ℝ) * (1 - 0.5) ^ n) = 2 := by
  have h := EarthScience.weighted_geometric_tsum_eq_inv
    (p := (0.5 : ℝ)) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / 0.5 = 2 by norm_num] at h
  exact h

/-- `p = 0.01`: the weighted series is `100`. -/
example :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((0.01 : ℝ) * (1 - 0.01) ^ n) = 100 :=
  EarthScience.weighted_geometric_tsum_one_hundredth

/-- Geometric series at `p = 1 / 4`: `∑' n, (3 / 4) ^ n = 4`. -/
example : ∑' n : ℕ, (1 - (0.25 : ℝ)) ^ n = 4 := by
  have h := EarthScience.geometric_tsum_one_sub_eq_inv
    (p := (0.25 : ℝ)) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / 0.25 = 4 by norm_num] at h
  exact h

/-- Boundary `p = 1`: only the `n = 0` term is nonzero, and the weighted series is `1`. -/
example :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((1 : ℝ) * (1 - 1) ^ n) = 1 := by
  have h := EarthScience.weighted_geometric_tsum_eq_inv
    (p := (1 : ℝ)) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / 1 = 1 by norm_num] at h
  exact h
