/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.OrderedGroupThreeClassesEmbeddingKourovka11Problem68
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Tactic.Push

open MathlibExt.GroupTheory.OrderedGroupThreeClassesEmbeddingKourovka11Problem68Wanted

-- Unpack the refutation as a single witness against every eligible target and homomorphism.
example : ∃ (G : Type) (_ : Group G) (_ : LinearOrder G) (_ : MulLeftMono G) (_ : MulRightMono G),
    ∀ (H : Type) [Group H] [LinearOrder H] [MulLeftMono H] [MulRightMono H],
      Nat.card (ConjClasses H) = 3 → ∀ f : G →* H, ¬ StrictMono f := by
  classical
  have h := orderedEmbedsInThreeClasses_refuted
  unfold orderedEmbedsInThreeClasses at h
  push Not at h
  obtain ⟨G, grp, ord, left, right, obstruct⟩ := h
  exact ⟨G, grp, ord, left, right, fun H _ _ _ _ ↦ obstruct H _ _ ‹_› ‹_›⟩

-- The infinite cyclic group has infinitely many singleton conjugacy classes.
example : Nat.card (ConjClasses (Multiplicative ℤ)) ≠ 3 := by
  rw [← Nat.card_congr (ConjClasses.mkEquiv (α := Multiplicative ℤ))]
  simp
