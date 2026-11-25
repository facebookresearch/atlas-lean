/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.BlockingWythoff

namespace MetaMathlibExt.BlockingWythoffTest

-- The first three positions on the vertical axis have zero, one, and two targets.
example : {q | wythoffTerminalMove 0 (0, 0) q ∧ q ∈ larssonSetTwo} = ∅ := by
  ext q
  simp [wythoffTerminalMove]

example : {q | wythoffTerminalMove 0 (0, 1) q ∧ q ∈ larssonSetTwo} = {(0, 0)} := by
  ext ⟨u, v⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq, wythoffTerminalMove]
  constructor
  · rintro ⟨⟨_, h | h | ⟨k, hk, hu, hv⟩⟩, _⟩ <;> omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨by decide, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩, larssonSetTwo_examples.1⟩

example : {q | wythoffTerminalMove 0 (0, 2) q ∧ q ∈ larssonSetTwo} = {(0, 0), (0, 1)} := by
  ext ⟨u, v⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
    wythoffTerminalMove]
  constructor
  · rintro ⟨⟨_, h | h | ⟨k, hk, hu, hv⟩⟩, _⟩ <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨by decide, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩, larssonSetTwo_examples.1⟩
    · exact ⟨⟨by decide, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩, larssonSetTwo_examples.2.1⟩

-- The first unequal Beatty pair also satisfies the stability bound with its piles reversed.
example : {q | wythoffTerminalMove 0 (6, 4) q ∧ q ∈ larssonSetTwo}.ncard ≤ 1 := by
  apply blockingWythoff_two_pPositions.1
  have hf : ⌊Real.goldenRatio⌋₊ = 1 :=
    (Nat.floor_eq_iff Real.goldenRatio_pos.le).mpr
      ⟨by exact_mod_cast Real.one_lt_goldenRatio.le, by norm_num [Real.goldenRatio_lt_two]⟩
  exact Or.inr ⟨1, Or.inr (by simp [Real.goldenRatio_sq, Nat.floor_add_one Real.goldenRatio_pos.le,
    hf])⟩

end MetaMathlibExt.BlockingWythoffTest
