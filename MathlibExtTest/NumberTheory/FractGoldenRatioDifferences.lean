/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FractGoldenRatioDifferences
import Mathlib.Tactic.LinearCombination

/-!
# Tests for differences of fractional parts of multiples of the golden ratio

The hypotheses of each case of `fract_goldenRatio_differences` hold for small indices: for
`i = 2`, `m₁ = 1`, `m₂ = 2` in case (i), for `i = 1`, `m₁ = 1`, `m₂ = 2` in case (ii) and for
`i = 3`, `m₁ = 1`, `m₂ = 5` in case (iii). In case (i) the bound is attained there, so the strict
inequality that the source prints fails.
-/

open MetaMathlibExt

/-- `1.6 < φ < 1.62`. -/
private lemma goldenRatio_bounds : 1.6 < Real.goldenRatio ∧ Real.goldenRatio < 1.62 := by
  have hsq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5 : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg 5
  constructor <;> simp only [Real.goldenRatio] <;> nlinarith

private lemma floor_one_mul_goldenRatio : ⌊((1 : ℤ) : ℝ) * Real.goldenRatio⌋ = 1 := by
  obtain ⟨h₁, h₂⟩ := goldenRatio_bounds
  rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith

private lemma floor_two_mul_goldenRatio : ⌊((2 : ℤ) : ℝ) * Real.goldenRatio⌋ = 3 := by
  obtain ⟨h₁, h₂⟩ := goldenRatio_bounds
  rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith

private lemma floor_five_mul_goldenRatio : ⌊((5 : ℤ) : ℝ) * Real.goldenRatio⌋ = 8 := by
  obtain ⟨h₁, h₂⟩ := goldenRatio_bounds
  rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith

-- Case (i) cannot be strict: for `i = 2` (`g₂ = F₆ / 2 = 4`), `m₁ = 1`, `m₂ = 2`, `x₁ = ⌊φ⌋ = 1`
-- and `x₂ = ⌊2φ⌋ = 3`, both sides equal `φ - 2`, because `φ ^ (-5) = 5φ - 8`.
example : ¬ ∀ (i : ℕ) (x₁ x₂ m₁ m₂ : ℤ), 1 ≤ i → Even (Nat.fib (3 * i) / 2) →
    2 * (x₂ - x₁) = (Nat.fib (3 * i) / 2 : ℕ) →
    x₁ = ⌊m₁ * Real.goldenRatio⌋ → x₂ = ⌊m₂ * Real.goldenRatio⌋ →
    Int.fract (m₂ * Real.goldenRatio) - Int.fract (m₁ * Real.goldenRatio) <
      (Real.goldenRatio ^ (-(3 * i : ℤ) + 1) - Real.goldenRatio) / 4 := by
  intro h
  have h5 : Real.goldenRatio ^ (-5 : ℤ) = 5 * Real.goldenRatio - 8 := by
    rw [zpow_neg, zpow_ofNat]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    linear_combination (5 * Real.goldenRatio ^ 4 - 3 * Real.goldenRatio ^ 3 +
      2 * Real.goldenRatio ^ 2 - Real.goldenRatio + 1) * Real.goldenRatio_sq
  have := h 2 1 3 1 2 (by norm_num) (by decide) (by decide) floor_one_mul_goldenRatio.symm
    floor_two_mul_goldenRatio.symm
  rw [← Int.self_sub_floor, ← Int.self_sub_floor, floor_one_mul_goldenRatio,
    floor_two_mul_goldenRatio] at this
  norm_num [h5] at this
  linarith

-- Case (ii) for `i = 1` (`g₁ = F₃ / 2 = 1`), `m₁ = 1`, `m₂ = 2`, `x₁ = ⌊φ⌋ = 1` and
-- `x₂ = ⌊2φ⌋ - 1 = 2`.
example : Int.fract ((2 : ℤ) * Real.goldenRatio) - Int.fract ((1 : ℤ) * Real.goldenRatio) <
    -0.28 := by
  obtain ⟨h, h'⟩ := (fract_goldenRatio_differences 1 le_rfl 1 2 1 2).2.1 (by decide)
    (by decide) floor_one_mul_goldenRatio.symm floor_two_mul_goldenRatio.symm
  exact h.trans h'

-- Case (iii) for `i = 3` (`g₃ = F₉ / 2 = 17`), `m₁ = 1`, `m₂ = 5`, `x₁ = ⌊φ⌋ - 1 = 0` and
-- `x₂ = ⌊5φ⌋ = 8`.
example : Int.fract ((5 : ℤ) * Real.goldenRatio) - Int.fract ((1 : ℤ) * Real.goldenRatio) <
    -0.52 := by
  obtain ⟨h, h'⟩ := (fract_goldenRatio_differences 3 (by norm_num) 0 8 1 5).2.2 (by decide)
    (by norm_num) (by decide) floor_one_mul_goldenRatio.symm floor_five_mul_goldenRatio.symm
  exact h.trans h'
