/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.StronglyMinimalCover
import Mathlib.SetTheory.Cardinal.Basic

namespace MathlibExt.Combinatorics.StronglyMinimalCoverOpenGardenProblem690Wanted.Tests

-- An empty edge rules out even an ordinary cover.
example : ¬ ∃ X, IsVertexCover ({∅} : Set (Finset ℕ)) X := by
  simp [IsVertexCover]

-- With no edges, the empty cover is strongly minimal.
example : IsStronglyMinimalCover (∅ : Set (Finset ℕ)) ∅ := by
  exact ⟨by simp [IsVertexCover], fun X _ ↦ by simp⟩

private def starEdges : Set (Finset ℕ) := {{0, 1}, {0, 2}}

-- The two leaves meet both edges, but exchanging them for the center improves the cover.
example : IsVertexCover starEdges {1, 2} ∧ ¬ IsStronglyMinimalCover starEdges {1, 2} := by
  refine ⟨by simp [IsVertexCover, starEdges], fun h ↦ ?_⟩
  have hle := h.2 {0} (by simp [IsVertexCover, starEdges])
  have hd : Disjoint ({1, 2} : Set ℕ) {0} := by simp
  rw [hd.sdiff_eq_left, hd.symm.sdiff_eq_left, Cardinal.mk_insert (by decide),
    Cardinal.mk_singleton, Cardinal.mk_singleton] at hle
  exact (by decide : ¬ 1 + 1 ≤ 1) (by exact_mod_cast hle)

end MathlibExt.Combinatorics.StronglyMinimalCoverOpenGardenProblem690Wanted.Tests
