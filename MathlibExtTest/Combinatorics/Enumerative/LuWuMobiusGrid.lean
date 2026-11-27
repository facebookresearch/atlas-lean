/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LuWuMobiusGrid
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.LuWuMobiusGrid` -/

namespace MathlibExtTest.LuWuMobiusGrid

open MetaMathlibExt

-- The seam edge `σ(0)` of the `2 × 3` Möbius grid joins `(0, 2)` to `(1, 0)`: the seam reverses
-- the rows.
example : MobiusGridIncident (M := 1) (N := 3) (.seam 0) ((0, 2) : MobiusGridVertex 1 3) ∧
    MobiusGridIncident (M := 1) (N := 3) (.seam 0) ((1, 0) : MobiusGridVertex 1 3) := by
  simp [MobiusGridIncident]

-- The vertical edge alone is a perfect matching of the `2 × 1` Möbius grid.
example : IsMobiusGridPerfectMatching (M := 1) (N := 1) {.vertical 0 0} := by
  intro v
  obtain ⟨a, c⟩ := v
  refine ⟨.vertical 0 0, ⟨Finset.mem_singleton_self _, ?_⟩, fun e he => ?_⟩
  · fin_cases a <;> fin_cases c <;> simp [MobiusGridIncident]
  · exact Finset.mem_singleton.mp he.1

-- The empty set is not a perfect matching: the vertex `(0, 0)` is not covered.
example : ¬IsMobiusGridPerfectMatching (M := 1) (N := 1) ∅ := by
  intro h
  obtain ⟨e, he, -⟩ := h ((0, 0) : MobiusGridVertex 1 1)
  simp at he

-- The Lu–Wu formula on the `2 × 1` Möbius grid. Its two vertices are joined by three labelled
-- edges (the vertical edge and the seam edges `σ(0)` and `σ(1)`), so there are three perfect
-- matchings, and the formula gives `Re((1 - i)(1 + 2i)) = 3`.
example : mobiusGridPerfectMatchingCount 1 1 = 3 := by
  have h := lu_wu_mobius_grid_perfect_matching_count (M := 1) (N := 1) one_pos one_pos odd_one
  have hsin : Real.sin (((4 * 1 - 1 : ℕ) : ℝ) * Real.pi / (2 * ((1 : ℕ) : ℝ))) = -1 := by
    rw [show ((4 * 1 - 1 : ℕ) : ℝ) * Real.pi / (2 * ((1 : ℕ) : ℝ)) = Real.pi / 2 + Real.pi by
      push_cast; ring, Real.sin_add_pi, Real.sin_pi_div_two]
  have hcos : Real.cos (((1 : ℕ) : ℝ) * Real.pi / (2 * ((1 : ℕ) : ℝ) + 1)) = 1 / 2 := by
    rw [show ((1 : ℕ) : ℝ) * Real.pi / (2 * ((1 : ℕ) : ℝ) + 1) = Real.pi / 3 by push_cast; ring,
      Real.cos_pi_div_three]
  simp only [Finset.Icc_self, Finset.prod_singleton, hsin, hcos] at h
  norm_num at h
  exact_mod_cast h

end MathlibExtTest.LuWuMobiusGrid
