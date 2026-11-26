/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.FastVanDerWaerdenGameIsSymmetricOfMakerWinsWithinCard

/-!
# Tests for symmetry forced by a fast Maker win

Applies the theorem to a two-element winning strategy and derives its contrapositive.
-/

namespace MathlibExtTest.Combinatorics.FastVanDerWaerdenGameIsSymmetricOfMakerWinsWithinCard

open Finset MetaMathlibExt.FastVanDerWaerdenGame

private theorem pair_wins : MakerWinsWithin {0, 1} 2 ∅ ∅ := by
  refine Or.inr ⟨0, by simp, by simp, ?_⟩
  intro y _ _ _
  refine Or.inr ⟨y + 1, by simp, by simp, ?_⟩
  intro z _ _ _
  refine ⟨y + 1, Nat.succ_pos y, 0, ?_⟩
  intro s hs
  simp only [mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact ⟨0, by simp, by simp⟩
  · exact ⟨y + 1, by simp, by simp⟩

example : IsSymmetric ({0, 1} : Finset ℚ) := by
  have h := isSymmetric_of_makerWinsWithin_card ({0, 1} : Finset ℕ)
    (by decide) (by simpa using pair_wins)
  simpa using h

example (S : Finset ℕ) (hS : 2 ≤ S.card)
    (h : ¬ IsSymmetric (S.image fun s : ℕ => (s : ℚ))) :
    ¬ MakerWinsWithin S S.card ∅ ∅ := by
  intro hw
  exact h (isSymmetric_of_makerWinsWithin_card S hS hw)

end MathlibExtTest.Combinatorics.FastVanDerWaerdenGameIsSymmetricOfMakerWinsWithinCard
