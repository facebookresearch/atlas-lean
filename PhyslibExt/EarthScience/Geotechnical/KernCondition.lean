/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Footing kern rule

## i. Overview

For a rigid strip footing of width `B > 0` (per unit
out-of-plane length) carrying vertical load `N > 0` and moment
`M` about the footing centerline, the linear full-contact edge
pressures are `N / B ± 6 * M / B ^ 2`. Both are nonnegative
exactly under the kern (middle-third) bound `|M / N| ≤ B / 6`.
The coefficient `6` is the centered-moment value: `M` is measured
about the centerline, and a moment taken about another axis must
be transferred to the centerline before applying the bound.

## ii. Key results

- `EarthScience.kern_condition_iff`: the full-contact admission
  condition in load coordinates.

## iii. Table of contents

- A. Kern condition

## iv. References

- J. E. Bowles, *Foundation Analysis and Design*, 5th edition,
  McGraw-Hill, 1996 (kern / middle-third rule for eccentrically
  loaded footings).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Kern condition -/

/-- Footing kern rule in load coordinates. For a rigid footing of
width `B > 0` carrying vertical load `N > 0` and moment `M` about the
footing centreline (per unit out-of-plane length), the two edge
pressures of the linear full-contact solution are
`N / B ± 6 * M / B ^ 2`. Both are nonnegative exactly when the
eccentricity ratio obeys the kern bound `|M / N| ≤ B / 6`. -/
theorem kern_condition_iff {N M B : ℝ} (hN : 0 < N) (hB : 0 < B) :
    (0 ≤ N / B - 6 * M / B ^ 2 ∧ 0 ≤ N / B + 6 * M / B ^ 2)
      ↔ |M / N| ≤ B / 6 := by
  have hB2 : (0:ℝ) < B ^ 2 := by positivity
  have hB' : B ≠ 0 := ne_of_gt hB
  have h6 : (0:ℝ) ≤ 6 := by norm_num
  have h6pos : (0:ℝ) < 6 := by norm_num
  have h6' : (6:ℝ) ≠ 0 := by norm_num
  have h1 : (0 ≤ N / B - 6 * M / B ^ 2 ∧ 0 ≤ N / B + 6 * M / B ^ 2)
      ↔ |6 * M / B ^ 2| ≤ N / B := by
    rw [abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : 0 ≤ 6 * M / B ^ 2 + N / B := by
        rw [add_comm]
        exact h2
      exact ⟨neg_le_iff_add_nonneg.mpr h2', sub_nonneg.mp h1⟩
    · rintro ⟨h1, h2⟩
      have h1' : 0 ≤ N / B + 6 * M / B ^ 2 := by
        rw [add_comm]
        exact neg_le_iff_add_nonneg.mp h1
      exact ⟨sub_nonneg.mpr h2, h1'⟩
  have hNB : N / B * B ^ 2 = N * B := by
    rw [div_mul_eq_mul_div, pow_two, ← mul_assoc, mul_div_cancel_right₀ _ hB']
  have h2 : |6 * M / B ^ 2| ≤ N / B ↔ |6 * M| ≤ N * B := by
    rw [abs_div, abs_of_pos hB2, div_le_iff₀ hB2, hNB]
  have e1 : (6:ℝ) * (B / 6 * N) = N * B := by
    rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_cancel_left₀ _ h6']
    exact mul_comm _ _
  have e3 : N * B / 6 = B / 6 * N := by
    rw [mul_div_assoc]
    exact mul_comm _ _
  have hdiv (x y : ℝ) (h : x ≤ y) : x / 6 ≤ y / 6 := by
    rw [div_le_iff₀ h6pos, div_mul_cancel₀ _ h6']
    exact h
  have h3 : |M / N| ≤ B / 6 ↔ |6 * M| ≤ N * B := by
    rw [abs_div, abs_of_pos hN, div_le_iff₀ hN, abs_mul, abs_of_nonneg h6]
    constructor
    · intro h
      calc (6:ℝ) * |M| ≤ 6 * (B / 6 * N) := mul_le_mul_of_nonneg_left h h6
        _ = N * B := e1
    · intro h
      calc |M| = 6 * |M| / 6 := (mul_div_cancel_left₀ _ h6').symm
        _ ≤ N * B / 6 := hdiv _ _ h
        _ = B / 6 * N := e3
  rw [h1, h2, h3]

end EarthScience
