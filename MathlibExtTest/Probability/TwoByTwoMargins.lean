/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.TwoByTwoMargins
import Mathlib.Tactic.NormNum

/-! # Examples for two-by-two cell bounds -/

open MetaMathlibExt

-- The lower endpoint is positive: the bottom-right cell must vanish at `x = 5`.
example : ∃ y z w : ℕ, 5 + y = 8 ∧ z + w = 2 ∧ 5 + z = 7 ∧ y + w = 3 := by
  exact (two_by_two_cell_bounds.1 (r₁ := 8) (r₂ := 2) (c₁ := 7) (c₂ := 3) (x := 5)
    (by decide)).2 (by decide)

-- The same margins do not admit a top-left count of four.
example : ¬ ∃ y z w : ℕ, 4 + y = 8 ∧ z + w = 2 ∧ 4 + z = 7 ∧ y + w = 3 := by
  intro h
  have hlo := ((two_by_two_cell_bounds.1 (r₁ := 8) (r₂ := 2) (c₁ := 7) (c₂ := 3) (x := 4)
    (by decide)).1 h).1
  norm_num at hlo

-- The real version attains a strictly interior, nonintegral value.
example : ∃ y z w : ℝ, 0 ≤ (11 / 2 : ℝ) ∧ 0 ≤ y ∧ 0 ≤ z ∧ 0 ≤ w ∧
    11 / 2 + y = 8 ∧ z + w = 2 ∧ 11 / 2 + z = 7 ∧ y + w = 3 := by
  exact (two_by_two_cell_bounds.2 (r₁ := 8) (r₂ := 2) (c₁ := 7) (c₂ := 3) (x := 11 / 2)
    (by norm_num)).2 ⟨by norm_num, by norm_num⟩
