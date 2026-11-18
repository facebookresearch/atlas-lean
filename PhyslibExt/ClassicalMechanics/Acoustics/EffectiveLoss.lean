/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Positivity

/-!
# Effective transmission loss of parallel patches

## i. Overview

For two equal-area patches with positive transmission coefficients
`τ1`, `τ2`, the effective loss `-10 * log10 ((τ1 + τ2) / 2)` of
the area-averaged coefficient lies between the two patch losses,
and for distinct coefficients it is strictly below the average of
the two decibel values: averaging decibels is not the effective
loss.

## ii. Key results

- `Acoustics.effective_loss_between`: the effective loss is
  between the patch losses.
- `Acoustics.effective_loss_lt_db_average`: the effective loss is
  strictly below the decibel average for distinct coefficients.

## iii. Table of contents

- A. Effective loss bounds

## iv. References

- Standard building-acoustics composite transmission loss
  (area-weighted transmission coefficients).
-/

@[expose] public section

namespace Acoustics

/-! ## A. Effective loss bounds -/

/-- Effective transmission loss of two parallel patches lies
between the two patch losses: for positive transmission
coefficients `τ1`, `τ2`, the loss `-10 * log10 ((τ1 + τ2) / 2)` of
the area-averaged coefficient is at least the smaller patch loss
`-10 * log10 (max τ1 τ2)` and at most the larger patch loss
`-10 * log10 (min τ1 τ2)`. -/
theorem effective_loss_between {τ1 τ2 : ℝ} (h1 : 0 < τ1)
    (h2 : 0 < τ2) :
    -10 * Real.logb 10 (max τ1 τ2)
        ≤ -10 * Real.logb 10 ((τ1 + τ2) / 2)
      ∧ -10 * Real.logb 10 ((τ1 + τ2) / 2)
        ≤ -10 * Real.logb 10 (min τ1 τ2) := by
  have h10 : (1:ℝ) < 10 := by norm_num
  have havg_pos : (0:ℝ) < (τ1 + τ2) / 2 := by linarith
  have hmin_le : min τ1 τ2 ≤ (τ1 + τ2) / 2 := by
    have a := min_le_left τ1 τ2
    have b := min_le_right τ1 τ2
    linarith
  have hmax_le : (τ1 + τ2) / 2 ≤ max τ1 τ2 := by
    have a := le_max_left τ1 τ2
    have b := le_max_right τ1 τ2
    linarith
  have hmin_pos : (0:ℝ) < min τ1 τ2 := lt_min h1 h2
  have e1 := Real.logb_le_logb_of_le h10 havg_pos hmax_le
  have e2 := Real.logb_le_logb_of_le h10 hmin_pos hmin_le
  refine ⟨?_, ?_⟩ <;> linarith

/-- Averaging decibel values is not the effective loss: for
distinct positive coefficients the area-averaged loss is strictly
below the average of the two patch losses (arithmetic-geometric
mean gap). Equal areas with `τ = 0.001` and `τ = 0.1` give about
`12.97 dB`, not the `20 dB` average of `30 dB` and `10 dB`. -/
theorem effective_loss_lt_db_average {τ1 τ2 : ℝ} (h1 : 0 < τ1)
    (h2 : 0 < τ2) (hne : τ1 ≠ τ2) :
    -10 * Real.logb 10 ((τ1 + τ2) / 2)
      < (-10 * Real.logb 10 τ1 + -10 * Real.logb 10 τ2) / 2 := by
  have h10 : (1:ℝ) < 10 := by norm_num
  have hprod_pos : (0:ℝ) < τ1 * τ2 := mul_pos h1 h2
  have hsq : τ1 * τ2 < ((τ1 + τ2) / 2) ^ 2 := by
    have hpos : (0:ℝ) < (τ1 - τ2) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    nlinarith [hpos]
  have hlog := Real.logb_lt_logb h10 hprod_pos hsq
  rw [Real.logb_mul (ne_of_gt h1) (ne_of_gt h2)] at hlog
  have hpow : Real.logb 10 (((τ1 + τ2) / 2) ^ 2)
      = 2 * Real.logb 10 ((τ1 + τ2) / 2) := by
    rw [Real.logb_pow]
    norm_num
  rw [hpow] at hlog
  linarith

end Acoustics
