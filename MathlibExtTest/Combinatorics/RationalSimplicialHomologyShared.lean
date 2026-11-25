/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.RationalSimplicialHomologyShared

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared

-- The middle vertex of the oriented triangle contributes the negative boundary coefficient.
example : let K := ({0, 1, 2} : Finset ℕ).powerset
    boundaryMatrix K 2 ⟨{0, 2}, by decide⟩ ⟨{0, 1, 2}, by decide⟩ = -1 := by decide +kernel

-- Augmentation distinguishes the void complex from the link of a facet.
example : IsRationallyAcyclic ∅ := by
  intro k
  have h (i : ℕ) : (boundaryMatrix ∅ i).rank = 0 := by
    have hle := (boundaryMatrix ∅ i).rank_le_card_width
    rw [Fintype.card_coe] at hle
    exact Nat.eq_zero_of_le_zero (by simpa only [facesOfCard, Finset.filter_empty,
      Finset.card_empty] using hle)
  unfold reducedBetti
  rw [h k, h (k - 1)]
  simp [facesOfCard]

example : ¬ IsRationallyAcyclic (link ({0} : Finset ℕ).powerset {0}) := by
  intro h
  have he : link ({0} : Finset ℕ).powerset {0} = {∅} := by decide
  rw [he] at h
  have hr := (boundaryMatrix {∅} 0).rank_le_card_width
  have hz : Fintype.card (facesOfCard {∅} (0 + 1)) = 0 := by decide
  rw [hz] at hr
  have hzero := h 0
  unfold reducedBetti at hzero
  rw [Nat.eq_zero_of_le_zero hr, show (facesOfCard {∅} 0).card = 1 by decide] at hzero
  norm_num at hzero
