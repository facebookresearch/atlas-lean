/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import MathlibExt.LinearAlgebra.Matrix.RankAddGeneral

open Matrix

/-! ## Independently computed ranks (Mathlib `rank_diagonal`, `rank_one`, `rank_zero`) -/

private def rankAddD₀ : Matrix (Fin 2) (Fin 2) ℚ := diagonal ![1, 0]
private def rankAddD₁ : Matrix (Fin 2) (Fin 2) ℚ := diagonal ![0, 1]

private theorem rank_rankAddD₀ : rankAddD₀.rank = 1 := by
  rw [rankAddD₀, rank_diagonal]; decide

private theorem rank_rankAddD₁ : rankAddD₁.rank = 1 := by
  rw [rankAddD₁, rank_diagonal]; decide

private theorem rankAddD₀_add_rankAddD₁ : rankAddD₀ + rankAddD₁ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rankAddD₀, rankAddD₁]

private theorem rank_rankAddD₀_add_rankAddD₁ : (rankAddD₀ + rankAddD₁).rank = 2 := by
  rw [rankAddD₀_add_rankAddD₁, rank_one, Fintype.card_fin]

-- Tightness: rank of the sum is `2` = `1 + 1`, so the bound cannot be improved.
example : (rankAddD₀ + rankAddD₁).rank = rankAddD₀.rank + rankAddD₁.rank := by
  rw [rank_rankAddD₀_add_rankAddD₁, rank_rankAddD₀, rank_rankAddD₁]

example : (rankAddD₀ + rankAddD₁).rank ≤ rankAddD₀.rank + rankAddD₁.rank :=
  rank_add_le rankAddD₀ rankAddD₁

-- Strictness: `rankAddD₀ + (-rankAddD₀) = 0` has rank `0 < 2`.
example : (rankAddD₀ + -rankAddD₀).rank < rankAddD₀.rank + (-rankAddD₀).rank := by
  rw [add_neg_cancel, rank_zero, rank_neg, rank_rankAddD₀]; norm_num

-- `rank_neg` agrees with an independent computation: `-1` is a unit, so its rank is `2`.
example : (-(1 : Matrix (Fin 2) (Fin 2) ℚ)).rank = 2 := by
  have h : IsUnit (-(1 : Matrix (Fin 2) (Fin 2) ℚ)) := isUnit_one.neg
  rw [rank_of_isUnit _ h, Fintype.card_fin]

example : (-(1 : Matrix (Fin 2) (Fin 2) ℚ)).rank = (1 : Matrix (Fin 2) (Fin 2) ℚ).rank :=
  rank_neg 1

-- Characteristic 2: `1 + 1 = 0` over `ZMod 2`, so the sum of two rank-2 matrices has rank 0.
example : ((1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + 1).rank = 0 := by
  have h : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + 1 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> rfl
  rw [h, rank_zero]

example : ((1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + 1).rank ≤
    (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).rank + (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).rank :=
  rank_add_le 1 1

/-! ## Generality of the index types -/

-- T76's real `Fin 2 × Fin 3` case is an instance.
example (A B : Matrix (Fin 2) (Fin 3) ℝ) : (A + B).rank ≤ A.rank + B.rank := rank_add_le A B

-- Rows need not be finite: the row index here is `ℕ`.
example (A B : Matrix ℕ (Fin 3) ℚ) : (A + B).rank ≤ A.rank + B.rank := rank_add_le A B

-- Boundary: with no columns every rank is `0` (`rank_le_width`), and the bound reads `0 ≤ 0`.
example (A B : Matrix (Fin 2) (Fin 0) ℚ) : (A + B).rank = 0 ∧ A.rank + B.rank = 0 := by
  have := rank_le_width (A + B); have := rank_le_width A; have := rank_le_width B
  omega

example (A B : Matrix (Fin 2) (Fin 0) ℚ) : (A + B).rank ≤ A.rank + B.rank := rank_add_le A B

-- Boundary: adding the zero matrix.
example (A : Matrix (Fin 2) (Fin 3) ℚ) :
    (A + 0).rank ≤ A.rank + (0 : Matrix (Fin 2) (Fin 3) ℚ).rank :=
  rank_add_le A 0

/-! ## Subtraction and the reverse triangle inequality -/

example : (rankAddD₀ - rankAddD₁).rank ≤ rankAddD₀.rank + rankAddD₁.rank :=
  rank_sub_le rankAddD₀ rankAddD₁

-- Reverse triangle inequality is tight here: `rank 1 = 2 = rank rankAddD₀ + rank (1 - rankAddD₀)`.
example : (1 - rankAddD₀ : Matrix (Fin 2) (Fin 2) ℚ) = rankAddD₁ := by
  rw [← rankAddD₀_add_rankAddD₁, add_sub_cancel_left]

example : (1 : Matrix (Fin 2) (Fin 2) ℚ).rank ≤ rankAddD₀.rank + (1 - rankAddD₀).rank :=
  rank_le_rank_add_rank_sub 1 rankAddD₀

/-! ## Finite sums -/

-- Non-vacuity of `rank_sum_le_card`: both summands have rank `≤ 1` (computed above), and the
-- bound `card = 2` is attained by their sum, the identity.
example : (∑ i ∈ (Finset.univ : Finset (Fin 2)), ![rankAddD₀, rankAddD₁] i).rank ≤
    (Finset.univ : Finset (Fin 2)).card :=
  rank_sum_le_card _ _ (by
    intro i _; fin_cases i
    · simp [rank_rankAddD₀]
    · simp [rank_rankAddD₁])

example : (∑ i : Fin 2, ![rankAddD₀, rankAddD₁] i).rank = 2 := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact rank_rankAddD₀_add_rankAddD₁

-- Boundary: the empty sum is `0`, rank `0`.
example (M : ℕ → Matrix (Fin 2) (Fin 2) ℚ) :
    (∑ i ∈ (∅ : Finset ℕ), M i).rank ≤ ∑ i ∈ (∅ : Finset ℕ), (M i).rank :=
  rank_sum_le ∅ M

example (M : ℕ → Matrix (Fin 2) (Fin 2) ℚ) : (∑ i ∈ (∅ : Finset ℕ), M i).rank = 0 := by
  simp
