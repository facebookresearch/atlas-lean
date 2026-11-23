/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.AffineRecurrence
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Tests for first-order affine recurrences

A stable recurrence (`a = 1/2`) with an explicit solution, the unit-root branch (`a = 1`), and an
oscillating recurrence (`a = -1`).
-/

@[expose] public section

namespace MathlibExtTest.Algebra.AffineRecurrence

open _root_.MathlibExt.AffineRecurrence

theorem test1_mem :
    IsAffineRecurrence (1 / 2 : ℝ) 1 (fun n : ℕ => (2 : ℝ) - 2 * (1 / 2) ^ n) := by
  intro n
  show (2 : ℝ) - 2 * (1 / 2) ^ (n + 1) = (1 / 2) * (2 - 2 * (1 / 2) ^ n) + 1
  rw [pow_succ]
  ring

example (x : ℕ → ℝ) (h : IsAffineRecurrence (1 / 2 : ℝ) 1 x) (h0 : x 0 = 0) :
    x 3 = 7 / 4 := by
  have h3 := h.eq_fixedPoint_add (by norm_num : (1 / 2 : ℝ) ≠ 1) 3
  rw [h0] at h3
  norm_num at h3
  exact h3

example (x : ℕ → ℝ) (h : IsAffineRecurrence (1 : ℝ) 3 x) (h0 : x 0 = 2) :
    x 4 = 14 := by
  have h4 := h.eq_add_nsmul_of_one 4
  rw [h0] at h4
  norm_num at h4
  exact h4

example (x : ℕ → ℝ) (h : IsAffineRecurrence (-1 : ℝ) 2 x) (h0 : x 0 = 0) :
    x 5 = 2 ∧ x 6 = 0 := by
  have h5 := h.eq_fixedPoint_add (by norm_num : (-1 : ℝ) ≠ 1) 5
  have h6 := h.eq_fixedPoint_add (by norm_num : (-1 : ℝ) ≠ 1) 6
  rw [h0] at h5 h6
  norm_num at h5 h6
  exact ⟨h5, h6⟩

theorem test_slope_zero (x : ℕ → ℝ) (h : IsAffineRecurrence (0 : ℝ) 5 x) (h0 : x 0 = 3) :
    x 0 = 3 ∧ x 1 = 5 ∧ x 4 = 5 := by
  have h1 := h.eq_fixedPoint_add (by norm_num : (0 : ℝ) ≠ 1) 1
  have h4 := h.eq_fixedPoint_add (by norm_num : (0 : ℝ) ≠ 1) 4
  rw [h0] at h1 h4
  norm_num at h1 h4
  exact ⟨h0, h1, h4⟩

theorem test_slope_zero_at_zero (x : ℕ → ℝ) (h : IsAffineRecurrence (0 : ℝ) 5 x) :
    x 0 = 5 / (1 - 0) + 0 ^ 0 * (x 0 - 5 / (1 - 0)) := by
  exact h.eq_fixedPoint_add (by norm_num : (0 : ℝ) ≠ 1) 0

theorem test_slope_zero_at_zero_simp (x : ℕ → ℝ) :
    5 / (1 - 0) + 0 ^ 0 * (x 0 - 5 / (1 - 0)) = x 0 := by
  norm_num

end MathlibExtTest.Algebra.AffineRecurrence
