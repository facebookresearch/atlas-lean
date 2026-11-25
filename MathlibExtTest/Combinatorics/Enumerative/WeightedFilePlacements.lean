/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.WeightedFilePlacements

open MetaMathlibExt

-- The empty placement is the unique contribution on the empty board.
example (m : ℕ) : weightedFileNumber m [] 0 = 1 := by
  have hempty : filePlacements [] = {∅} := by decide
  simp [weightedFileNumber, hempty, Finset.filter_singleton, filePlacementWeight]

-- The two full placements on the nonempty columns have weights -2 and 1.
example : weightedFileNumber 3 [0, 1, 2] 2 = -1 := by decide

example : ∑ k ∈ Finset.range 4,
    weightedFileNumber 3 [0, 1, 2] k * mFallingFactorial (-2) (3 - k) 3 = -48 := by
  exact (weightedFileNumber_factorization 3 (by decide) [0, 1, 2] (by decide) (-2)).trans
    (by decide)

-- The left column has only one cell in the chosen level, but the next column has both rows.
example : (filePlacementBlock 2 [1, 2] {(0, 0), (1, 1)} 0 (0, 0)).card = 2 := by
  decide

-- The leftmost cell is fixed on the top row; the other two cells vary independently.
example : (filePlacementBlock 2 [2, 2, 2] {(0, 1), (1, 0), (2, 0)} 0 (0, 1)).card = 4 := by
  decide

-- At level one, the outside cell and the leftmost cell of the level both stay fixed.
set_option maxRecDepth 4096 in
example : filePlacementBlock 2 [1, 4, 4] {(0, 0), (1, 3), (2, 2)} 1 (1, 3) =
    {{(0, 0), (1, 3), (2, 2)}, {(0, 0), (1, 3), (2, 3)}} := by
  decide

-- The leftmost column is partial, but the other column can use either row.
example : ∑ F ∈ filePlacementBlock 2 [1, 2] {(0, 0), (1, 1)} 0 (0, 0),
    filePlacementWeight 2 F = 0 := by
  refine sum_filePlacementWeight_block 2 (by decide) [1, 2] ?_ _ (by decide) (by decide) 0 (0, 0) ?_
  · unfold IsSingletonBoard
    decide
  · refine ⟨by decide, ?_, by decide, by decide, by simp⟩
    intro k hk
    by_cases h : k = 0
    · subst k
      exact Or.inr ⟨rfl, le_rfl⟩
    · simp [Finset.filter_insert, Finset.filter_singleton, Ne.symm h] at hk

-- Two columns vary in level one, and the cell in level zero stays fixed.
example : ∑ F ∈ filePlacementBlock 2 [1, 3, 4, 4] {(0, 0), (1, 2), (2, 3), (3, 3)} 1 (1, 2),
    filePlacementWeight 2 F = 0 := by
  apply sum_filePlacementWeight_block 2 (by decide)
  · unfold IsSingletonBoard
    decide
  · rw [filePlacements, Finset.mem_filter, Finset.mem_powerset]
    decide
  · simp only [levelRookPlacements, Finset.mem_filter, not_and]
    intro _
    decide
  · refine ⟨by decide, ?_, by decide, by decide, ?_⟩
    · intro k hk
      by_cases h : k = 1
      · subst k
        exact Or.inr ⟨rfl, le_rfl⟩
      · by_cases h₀ : k = 0
        · subst k
          simp [Finset.filter_insert, Finset.filter_singleton] at hk
        · simp [Finset.filter_insert, Finset.filter_singleton, Ne.symm h, Ne.symm h₀] at hk
    · intro c hc hlevel
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact (by decide : ¬ 0 / 2 = (1 : ℕ)) hlevel |>.elim
      · decide
      · decide
      · decide
