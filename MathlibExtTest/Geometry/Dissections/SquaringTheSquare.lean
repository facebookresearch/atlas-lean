/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Dissections.SquaringTheSquare

/-! # Boundary coverage for the dissection of the unit square -/

open Set MathlibExt.Geometry.ScottishBook59Wanted

-- Every point of the closed top edge, including its two corners, lies on a tile's top edge.
example : ∃ (n : ℕ) (x y s : Fin n → ℝ), 1 < n ∧ (∀ i, 0 < s i) ∧
    (∀ i j, i ≠ j → s i ≠ s j) ∧
    ∀ u ∈ Icc (0 : ℝ) 1, ∃ i, u ∈ Icc (x i) (x i + s i) ∧ y i + s i = 1 := by
  obtain ⟨n, x, y, s, hn, hpos, hdistinct, hcover, _⟩ := squaringTheSquareDistinctSquares
  refine ⟨n, x, y, s, hn, hpos, hdistinct, ?_⟩
  intro u hu
  have htop : (u, 1) ∈ Icc ((0, 0) : ℝ × ℝ) (1, 1) :=
    ⟨⟨hu.1, zero_le_one⟩, hu.2, le_rfl⟩
  rw [← hcover, mem_iUnion] at htop
  obtain ⟨i, hlo, hhi⟩ := htop
  have hcorner : (x i + s i, y i + s i) ∈ Icc ((0, 0) : ℝ × ℝ) (1, 1) := by
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, right_mem_Icc.mpr
      ⟨le_add_of_nonneg_right (hpos i).le, le_add_of_nonneg_right (hpos i).le⟩⟩
  exact ⟨i, ⟨hlo.1, hhi.1⟩, le_antisymm hcorner.2.2 hhi.2⟩
