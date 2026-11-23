/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.KCenter
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Three reals pairwise at least `3` apart, more than `2 * 1`, cannot all lie within `1` of two
centers. -/
example (c₁ c₂ : ℝ) : ¬ ∀ x ∈ ({0, 3, 6} : Finset ℝ), dist x c₁ ≤ 1 ∨ dist x c₂ ≤ 1 := by
  intro hcov
  refine kcenter_separation_impossible (k := 2) (r := 1) {c₁, c₂} {0, 3, 6}
    Finset.card_le_two ?_ ?_ ?_
  · rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_pair (by norm_num)]
    norm_num
  · intro x hx
    rcases hcov x hx with h | h
    · exact ⟨c₁, by simp, h⟩
    · exact ⟨c₂, by simp, h⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | norm_num [Real.dist_eq]

/-- The separation must be strict: `-1` and `1` are exactly `2 * 1` apart and both lie within
`1` of the center `0`. -/
example : dist (-1 : ℝ) 0 ≤ 1 ∧ dist (1 : ℝ) 0 ≤ 1 ∧ dist (-1 : ℝ) 1 = 2 * 1 := by
  norm_num [Real.dist_eq]

end
