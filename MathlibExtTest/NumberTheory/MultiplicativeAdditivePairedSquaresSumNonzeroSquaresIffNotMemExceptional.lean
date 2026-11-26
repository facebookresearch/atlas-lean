/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresSumNonzeroSquaresIffNotMemExceptional
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.MultiplicativeAdditiveEightSquares
import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquares
import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresRigidity
import MathlibExt.NumberTheory.MultiplicativeAdditiveThreePairedSquares
import MathlibExt.NumberTheory.SixAndEightNonzeroSquares

namespace MathlibExtTest.NumberTheory.MultiplicativeAdditivePairedSquaresSumNonzeroSquaresIffNotMemExceptional

open MetaMathlibExt

-- 7 is a sum of four nonzero squares: 7 = 2² + 1² + 1² + 1².
example : ∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 7 := by
  rw [sum_nonzero_squares_iff_not_mem_exceptional 4 7 (by decide) (by decide),
    ite_eq_left rfl]
  intro hcon
  rw [Set.mem_union] at hcon
  rcases hcon with hfin | ⟨r, hr⟩
  · simp at hfin
  · rcases hr with hr | hr | hr <;> omega

-- 9 is in the finite part of E₄, so not a sum of four nonzero squares.
example : ¬∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 9 := by
  rw [sum_nonzero_squares_iff_not_mem_exceptional 4 9 (by decide) (by decide),
    ite_eq_left rfl]
  intro h
  exact h (Or.inl (by simp))

-- 8 = 2 · 4¹ is in the infinite part of E₄, so not a sum of four nonzero squares.
example : ¬∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 8 := by
  rw [sum_nonzero_squares_iff_not_mem_exceptional 4 8 (by decide) (by decide),
    ite_eq_left rfl]
  intro h
  exact h (Or.inr ⟨1, Or.inl (by decide)⟩)

-- 8 is a sum of five nonzero squares: 8 = 2² + 1² + 1² + 1² + 1².
example : ∃ a : Fin 5 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 8 := by
  rw [sum_nonzero_squares_iff_not_mem_exceptional 5 8 (by decide) (by decide),
    ite_eq_right (by decide : ¬(5 : ℕ) = 4), ite_eq_left rfl]
  simp

-- 9 is in E₅, so not a sum of five nonzero squares.
example : ¬∃ a : Fin 5 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 9 := by
  rw [sum_nonzero_squares_iff_not_mem_exceptional 5 9 (by decide) (by decide),
    ite_eq_right (by decide : ¬(5 : ℕ) = 4), ite_eq_left rfl]
  intro h
  exact h (by simp)

-- 9 = 6 + 3 is a sum of six nonzero squares.
example : ∃ a : Fin 6 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 9 := by
  rw [sum_nonzero_squares_iff_not_mem_exceptional 6 9 (by decide) (by decide),
    ite_eq_right (by decide : ¬(6 : ℕ) = 4), ite_eq_right (by decide : ¬(6 : ℕ) = 5)]
  intro hcon
  rw [Set.mem_union] at hcon
  rcases hcon with hI | hE
  · simp [Set.mem_Ico] at hI
  · simp at hE

-- 7 = 6 + 1 is in E₆, so not a sum of six nonzero squares.
example : ¬∃ a : Fin 6 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 7 := by
  rw [sum_nonzero_squares_iff_not_mem_exceptional 6 7 (by decide) (by decide),
    ite_eq_right (by decide : ¬(6 : ℕ) = 4), ite_eq_right (by decide : ¬(6 : ℕ) = 5)]
  intro h
  exact h (Or.inr (by simp))

-- 21 = 7 + 14 is a sum of seven nonzero squares (large case).
example : ∃ a : Fin 7 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 21 := by
  rw [sum_nonzero_squares_iff_not_mem_exceptional 7 21 (by decide) (by decide),
    ite_eq_right (by decide : ¬(7 : ℕ) = 4), ite_eq_right (by decide : ¬(7 : ℕ) = 5)]
  intro hcon
  rw [Set.mem_union] at hcon
  rcases hcon with hI | hE
  · simp [Set.mem_Ico] at hI
  · simp at hE

end MathlibExtTest.NumberTheory.MultiplicativeAdditivePairedSquaresSumNonzeroSquaresIffNotMemExceptional
