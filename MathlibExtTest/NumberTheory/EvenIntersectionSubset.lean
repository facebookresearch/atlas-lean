/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Ring.Parity
import MathlibExt.NumberTheory.EvenIntersectionSubset

open MetaMathlibExt

-- The family can be empty; in that case the full interval is an admissible witness.
example (X : Fin 0 → Finset ℕ) :
    ∃ Y : Finset ℕ, Y ⊆ Finset.Icc 1 2 ∧ Y.card = 2 ∧ ∀ i, Even (Y ∩ X i).card :=
  exists_card_even_inter (m := 2) (by decide) (by decide) X

-- At the one-set threshold the point `1` must be omitted. Points outside the interval
-- are allowed in the given set and do not affect the intersection.
example : ∃ Y : Finset ℕ, Y ⊆ Finset.Icc 1 3 ∧ Y.card = 2 ∧ 1 ∉ Y := by
  obtain ⟨Y, hY, hcard, hEven⟩ := exists_card_even_inter (a := 1) (m := 2)
    (by decide) (by decide) (fun _ => ({1, 7} : Finset ℕ))
  refine ⟨Y, hY, hcard, fun hOne => ?_⟩
  have hSeven : 7 ∉ Y := fun h => (by decide : 7 ∉ Finset.Icc 1 3) (hY h)
  have hInter : Y ∩ ({1, 7} : Finset ℕ) = {1} := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, rfl | rfl⟩
      · rfl
      · exact (hSeven hj).elim
    · rintro rfl
      exact ⟨hOne, Or.inl rfl⟩
  have h := hEven 0
  rw [hInter, Finset.card_singleton] at h
  exact (by decide : ¬ Even (1 : ℕ)) h

-- At the two-set threshold the full interval meets both sets evenly but is too large.
example :
    let X (i : Fin 2) : Finset ℕ := if i = 0 then {3, 4, 5, 6} else {2, 4}
    ∃ Y : Finset ℕ, Y ⊆ Finset.Icc 1 6 ∧ Y.card = 4 ∧ ∀ i, Even (Y ∩ X i).card := by
  dsimp only
  exact exists_card_even_inter (a := 2) (m := 4) (by decide) (by decide) _
