/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.LehmerBoundsFormula

open MetaMathlibExt

-- No free coordinate: κ of the empty list is 0, not 1.
example : lehmerLower [] 0 = 0 ∧ lehmerUpper [] 0 = 0 := by
  constructor
  · have h := (lehmerLower_upper_length (t := []) (by simp)).1
    simpa [lehmerKappa] using h
  · simpa using lehmerLower_upper_formula.2.1 0

example : lehmerLower [] 1 = 1 ∧ lehmerUpper [] 1 = 1 := by
  exact ⟨lehmerLower_upper_formula.1 1 le_rfl, by norm_num [lehmerLower_upper_formula.2.1]⟩

example : lehmerLower [] 3 = 1 ∧ lehmerUpper [] 3 = 7 := by
  exact ⟨lehmerLower_upper_formula.1 3 (by decide), by norm_num [lehmerLower_upper_formula.2.1]⟩

-- For a proper nonempty prefix, the denominator and the repeated last entry both matter.
example : lehmerLower [2, 3] 4 = 3 ∧ lehmerUpper [2, 3] 4 = 53 / 8 := by
  obtain ⟨hL, hU⟩ := lehmerLower_upper_formula.2.2 [2, 3] 4 (by simp)
    (by norm_num) (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> norm_num) (by decide)
  exact ⟨by norm_num at hL; exact hL, by norm_num at hU; exact hU⟩

-- A full-length singleton has κ = 1, not the product ratio 2.
example : lehmerLower [2] 1 = 1 ∧ lehmerUpper [2] 1 = 1 := by
  have hL := (lehmerLower_upper_length (t := [2]) (by simp)).1
  have hU := (lehmerLower_upper_formula.2.2 [2] 1 (by simp) (by simp)
    (by simp) (by decide)).2
  exact ⟨by norm_num [lehmerKappa] at hL; exact hL, by norm_num at hU; exact hU⟩

example : lehmerUpper [2, 3] 2 = 5 / 2 := by
  have h := (lehmerLower_upper_formula.2.2 [2, 3] 2 (by simp) (by norm_num)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> norm_num) (by decide)).2
  norm_num at h
  exact h
