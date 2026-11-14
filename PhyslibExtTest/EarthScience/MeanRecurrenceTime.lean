/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.MeanRecurrenceTime

/-!
# Mean-recurrence-time checks

Concrete consumers of `PhyslibExt.EarthScience.MeanRecurrenceTime`:
a fair-coin exceedance (`p = 1 / 2`) recurs every `2` years on average,
the 100-year flood recurs every `100` years on average, and the boundary
`p = 1` (exceedance every year) recurs every `1` year.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete recurrence times
- B. Boundary

## iv. References

- `PhyslibExt.EarthScience.MeanRecurrenceTime`
-/

/-- `p = 1 / 2`: mean recurrence time is `2` years. -/
example :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((0.5 : ℝ) * (1 - 0.5) ^ n) = 2 := by
  have h := EarthScience.mean_recurrence_time_eq_inv_exceedance_prob
    (p := (0.5 : ℝ)) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / 0.5 = 2 by norm_num] at h
  exact h

/-- `p = 0.01`: the 100-year flood has mean recurrence time `100` years. -/
example :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((0.01 : ℝ) * (1 - 0.01) ^ n) = 100 :=
  EarthScience.mean_recurrence_hundred_year

/-- Survival sum at `p = 1 / 4`: `∑' n, (3 / 4) ^ n = 4`. -/
example : ∑' n : ℕ, (1 - (0.25 : ℝ)) ^ n = 4 := by
  have h := EarthScience.mean_recurrence_survival_sum
    (p := (0.25 : ℝ)) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / 0.25 = 4 by norm_num] at h
  exact h

/-- Boundary `p = 1`: exceedance every year, mean recurrence time `1` year. -/
example :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((1 : ℝ) * (1 - 1) ^ n) = 1 := by
  have h := EarthScience.mean_recurrence_time_eq_inv_exceedance_prob
    (p := (1 : ℝ)) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / 1 = 1 by norm_num] at h
  exact h
