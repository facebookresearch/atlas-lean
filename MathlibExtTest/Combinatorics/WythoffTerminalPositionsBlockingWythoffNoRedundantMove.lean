/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WythoffTerminalPositionsBlockingWythoffNoRedundantMove

/-!
# Concrete instances of the no-redundant-move theorem

These examples apply the theorem to horizontal, vertical and diagonal move vectors.
-/

namespace MathlibExtTest.Combinatorics.WythoffTerminalPositionsBlockingWythoffNoRedundantMove

open MetaMathlibExt

example : ∃ x ∉ larssonSetTwo,
    {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo ∧
      ¬(y.1 + 1 = x.1 ∧ y.2 + 0 = x.2)}.ncard < 2 := by
  exact (blockingWythoff_no_redundant_move (1, 0)
    ⟨1, by decide, Or.inl rfl⟩).1

example : ∃ x ∉ larssonSetThree,
    {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetThree ∧
      ¬(y.1 + 0 = x.1 ∧ y.2 + 3 = x.2)}.ncard ≤ 2 := by
  obtain ⟨x, hx, hc⟩ := (blockingWythoff_no_redundant_move (0, 3)
    ⟨3, by decide, Or.inr (Or.inl rfl)⟩).2
  exact ⟨x, hx, Nat.lt_succ_iff.mp hc⟩

example : ∃ x ∉ larssonSetTwo,
    {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo ∧
      ¬(y.1 + 5 = x.1 ∧ y.2 + 5 = x.2)}.ncard ≤ 1 := by
  obtain ⟨x, hx, hc⟩ := (blockingWythoff_no_redundant_move (5, 5)
    ⟨5, by decide, Or.inr (Or.inr rfl)⟩).1
  exact ⟨x, hx, Nat.lt_succ_iff.mp hc⟩

end MathlibExtTest.Combinatorics.WythoffTerminalPositionsBlockingWythoffNoRedundantMove
