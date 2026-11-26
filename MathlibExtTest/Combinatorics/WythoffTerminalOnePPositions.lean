/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WythoffTerminalOnePPositions

namespace MetaMathlibExt.WythoffTerminalOnePPositionsTest

-- The reversed first mex pair is stable.
example (q : ℕ × ℕ) (hm : wythoffTerminalMove 1 (4, 2) q) :
    q ∉ wythoffTerminalPSet 1 :=
  wythoffTerminal_one_pPositions.1 _ _
    (Or.inr ⟨0, Or.inr (by simp [wythoffMexA_zero, wythoffMexB_zero])⟩) hm

-- The first nonterminal position on the main diagonal is absorbed by the terminal set.
example : ∃ q, wythoffTerminalMove 1 (1, 1) q ∧ q ∈ wythoffTerminalPSet 1 := by
  apply wythoffTerminal_one_pPositions.2
  rintro (ht | ⟨n, h | h⟩)
  · exact (by decide : ¬ (1 + 1 ≤ (1 : ℕ))) ht
  · obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    rw [wythoffMexB] at h₂
    omega
  · obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    rw [wythoffMexB] at h₁
    omega

-- The smaller pile is `a₁`, but the larger pile is below `b₁`.
-- This position can move diagonally to `(a₀, b₀)` rather than along a row to its partner.
example : ∃ q, wythoffTerminalMove 1 (3, 5) q ∧ q ∈ wythoffTerminalPSet 1 := by
  apply wythoffTerminal_one_pPositions.2
  rintro (ht | ⟨n, h | h⟩)
  · exact (by decide : ¬ (3 + 5 ≤ (1 : ℕ))) ht
  · obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    rw [wythoffMexB] at h₂
    have hn : n = 0 := by omega
    rw [hn, wythoffMexA_zero] at h₁
    omega
  · obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    rw [wythoffMexB] at h₁
    omega

-- In the preceding case the matching gap is realized by the first mex pair.
example : wythoffTerminalMove 1 (3, 5) (2, 4) ∧ (2, 4) ∈ wythoffTerminalPSet 1 :=
  ⟨⟨by decide, Or.inr (Or.inr ⟨1, by decide⟩)⟩,
    Or.inr ⟨0, Or.inl (by simp [wythoffMexA_zero, wythoffMexB_zero])⟩⟩

end MetaMathlibExt.WythoffTerminalOnePPositionsTest
