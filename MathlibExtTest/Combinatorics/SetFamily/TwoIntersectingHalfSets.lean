/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.TwoIntersectingHalfSets
import Mathlib.Data.Fintype.Powerset

/-! # Boundary and sharpness tests for 2-intersecting half-size sets -/

namespace MathlibExtTest.TwoIntersectingHalfSets

open Finset MathlibExt.Combinatorics.TwoIntersectingHalfSetsErdosProblem83Wanted

-- At n = 0 the diagonal intersection condition forces the family to be empty.
example (F : Finset (Finset (Fin 0))) (h : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    F = ∅ := by
  have hu (A : Finset (Fin 0)) : A.card = 0 := Nat.eq_zero_of_le_zero (by
    simpa using card_le_univ A)
  have hb := twoIntersectingHalfSetsBound_holds 0 F (fun A _ ↦ hu A) h
  change 2 * F.card + 1 ≤ 1 at hb
  exact card_eq_zero.mp (by omega)

-- On eight points the four-sets containing at least three of the first four points attain 17.
example : IsGreatest {m : ℕ | ∃ F : Finset (Finset (Fin 8)), F.card = m ∧
    (∀ A ∈ F, A.card = 4) ∧ (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card)} 17 := by
  let P : Finset (Fin 8) := {0, 1, 2, 3}
  let F := (univ.powersetCard 4).filter (fun A ↦ 3 ≤ (A ∩ P).card)
  constructor
  · refine ⟨F, by decide, fun A ha ↦ (mem_powersetCard.mp (mem_filter.mp ha).1).2, ?_⟩
    intro A ha B hb
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    have hsum := card_inter_add_card_union (A ∩ P) (B ∩ P)
    have hle := card_le_card (show (A ∩ P) ∪ (B ∩ P) ⊆ P from
      union_subset inter_subset_right inter_subset_right)
    have hi := card_le_card (show (A ∩ P) ∩ (B ∩ P) ⊆ A ∩ B from
      inter_subset_inter inter_subset_left inter_subset_left)
    have hp : P.card = 4 := by decide
    omega
  · rintro m ⟨G, rfl, hu, hg⟩
    have hb := twoIntersectingHalfSetsBound_holds 2 G hu hg
    change 2 * G.card + 36 ≤ 70 at hb
    omega

end MathlibExtTest.TwoIntersectingHalfSets
