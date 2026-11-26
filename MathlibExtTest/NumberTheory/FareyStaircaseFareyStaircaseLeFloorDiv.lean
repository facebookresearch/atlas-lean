/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FareyStaircaseFareyStaircaseLeFloorDiv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.FareyStaircaseFareyStaircaseLeFloorDiv` -/

namespace MathlibExtTest.NumberTheory.FareyStaircaseFareyStaircaseLeFloorDiv

open MetaMathlibExt

example : fareyStaircase 2 (1/2 : ℝ) ≤ 1/2 := by
  have h := fareyStaircase_le_floor_div (n := 2) (by norm_num) (1/2 : ℝ)
  have hfloor : (⌊(((2:ℕ)):ℝ) * (1/2 : ℝ)⌋ : ℝ) = 1 := by norm_num
  have h1 : fareyStaircase 2 (1/2 : ℝ) ≤ (⌊(((2:ℕ)):ℝ) * (1/2 : ℝ)⌋ : ℝ) / 2 := h.1
  rw [hfloor] at h1
  norm_num at h1 ⊢
  exact h1

example : (1/2 : ℝ) ≤ Real.log 2 := by
  have h := fareyStaircase_le_floor_div (n := 2) (by norm_num) (1/2 : ℝ)
  have hfarey : fareyStaircase 2 (1/2 : ℝ) = 1/4 := by
    unfold fareyStaircase
    norm_num [Finset.sum_Icc_succ_top]
  have hfloor : (⌊(((2:ℕ)):ℝ) * (1/2 : ℝ)⌋ : ℝ) = 1 := by norm_num
  have h2 := h.2
  rw [hfarey, hfloor] at h2
  norm_num at h2 ⊢
  linarith

example (x : ℝ) : fareyStaircase 1 x = (⌊x⌋ : ℝ) := by
  have h := fareyStaircase_le_floor_div (n := 1) (by norm_num) x
  have h1x : (((1:ℕ)) : ℝ) * x = x := by norm_num
  rw [h1x] at h
  simp at h
  exact le_antisymm h.1 h.2

end MathlibExtTest.NumberTheory.FareyStaircaseFareyStaircaseLeFloorDiv
