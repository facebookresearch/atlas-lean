/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CohenMacaulayPartitionability

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared
open MathlibExt.Combinatorics.CohenMacaulayPartitionabilityAMR156Problem0005Wanted

namespace MathlibExtTest.Combinatorics.CohenMacaulayPartitionability

-- The empty face is itself a facet of this complex. Its sole interval covers it.
example : IsPartitionable {∅} := by
  refine ⟨fun _ => ∅, by simp, ?_⟩
  intro σ hσ
  obtain rfl := Finset.mem_singleton.mp hσ
  refine ⟨∅, ⟨⟨by simp, ?_⟩, by simp⟩, ?_⟩
  · intro G hG _
    exact Finset.mem_singleton.mp hG
  · intro F hF
    exact Finset.mem_singleton.mp hF.1.1

example : ∃ K, IsSimplicialComplex K ∧ IsPure K ∧ IsCohenMacaulayOverRat K ∧
    ¬ IsPartitionable K := by
  simpa only [cohenMacaulayPartitionable, Classical.not_forall, exists_prop] using
    cohenMacaulayPartitionable_refuted

private def twoPoints : Finset (Finset ℕ) := {∅, {0}, {1}}

private def twoEdges : Finset (Finset ℕ) := {∅, {0}, {1}, {0, 1}, {2}, {3}, {2, 3}}

-- Two points are Cohen–Macaulay: below dimension 0 only the reduced homology in degree -1 must
-- vanish, and the augmentation row has rank one. The links of the vertices are `{∅}`.
example : IsCohenMacaulayOverRat twoPoints := by
  intro F hF k hk
  simp only [twoPoints, Finset.mem_insert, Finset.mem_singleton] at hF
  rcases hF with rfl | rfl | rfl
  · have hl : link twoPoints ∅ = twoPoints := by decide
    have htop : topCard twoPoints = 1 := by decide
    rw [hl, htop] at hk
    rw [hl, Nat.lt_one_iff.mp hk]
    have hrank : (boundaryMatrix twoPoints 0).rank = 1 := by
      apply le_antisymm
      · have hle := (boundaryMatrix twoPoints 0).rank_le_card_height
        rwa [show Fintype.card (facesOfCard twoPoints 0) = 1 by decide] at hle
      · have hsub : (boundaryMatrix twoPoints 0).submatrix
            (fun _ : Unit => ⟨∅, by decide⟩) (fun _ : Unit => ⟨{0}, by decide⟩) = 1 := by
          ext i j
          rw [Matrix.submatrix_apply, Subsingleton.elim i j, Matrix.one_apply_eq]
          decide +kernel
        calc 1 = (1 : Matrix Unit Unit ℚ).rank := by simp
          _ ≤ _ := hsub ▸ Matrix.rank_submatrix_le _ _ _
    simp only [reducedBetti, hrank, ↓reduceIte, show (facesOfCard twoPoints 0).card = 1 by decide]
    norm_num
  · rw [show link twoPoints {0} = {∅} by decide, show topCard {∅} = 0 by decide] at hk
    exact absurd hk (Nat.not_lt_zero k)
  · rw [show link twoPoints {1} = {∅} by decide, show topCard {∅} = 0 by decide] at hk
    exact absurd hk (Nat.not_lt_zero k)

-- Two disjoint edges form a pure complex that is not Cohen–Macaulay: it is disconnected, so its
-- reduced homology in degree 0 does not vanish below its dimension 1.
example : IsPure twoEdges ∧ ¬ IsCohenMacaulayOverRat twoEdges := by
  constructor
  · refine ⟨2, fun F hF => ?_⟩
    have h : ∀ F ∈ twoEdges, (∀ G ∈ twoEdges, F ⊆ G → G = F) → F.card = 2 := by decide
    exact h F hF.1 hF.2
  · intro hcm
    have hl : link twoEdges ∅ = twoEdges := by decide
    have h := hcm ∅ (by decide) 1 (by rw [hl]; decide)
    rw [hl] at h
    -- The augmentation has rank at most one and the edge boundary rank at most two.
    have h0 := (boundaryMatrix twoEdges (1 - 1)).rank_le_card_height
    have h1 := (boundaryMatrix twoEdges 1).rank_le_card_width
    rw [show Fintype.card (facesOfCard twoEdges (1 - 1)) = 1 by decide] at h0
    rw [show Fintype.card (facesOfCard twoEdges (1 + 1)) = 2 by decide] at h1
    simp only [reducedBetti, one_ne_zero, ↓reduceIte,
      show (facesOfCard twoEdges 1).card = 4 by decide] at h
    omega

end MathlibExtTest.Combinatorics.CohenMacaulayPartitionability
