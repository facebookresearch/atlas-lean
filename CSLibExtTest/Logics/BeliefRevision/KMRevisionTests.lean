/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.BeliefRevision.KMRevision

/-!
# Tests for KM belief revision

Two-atom boundary checks for Dalal revision: revising by an inconsistent and
by a consistent sentence, and the empty knowledge base.
-/

@[expose] public section

namespace Cslib.BeliefRevision.KMRevisionTest

open Cslib.BeliefRevision Finset

/-- With two atoms `p q : Fin 2`, revising "`p` is true" by "`p` is false and
`q` is true" under Dalal gives exactly the interpretation `p = false`,
`q = true` when it is the unique closest model of the new sentence. -/
theorem dalal_two_atoms :
    dalalRev (σ := Fin 2)
        (Finset.univ.filter fun I => I 0 = true)
        (Finset.univ.filter fun I => I 0 = false ∧ I 1 = true)
      = {fun a => decide (a = 1)} := by
  have hB : (Finset.univ.filter fun I : Fin 2 → Bool => I 0 = false ∧ I 1 = true)
      = {fun a => decide (a = 1)} := by decide
  have hBNonempty : (Finset.univ.filter
      fun I : Fin 2 → Bool => I 0 = false ∧ I 1 = true).Nonempty := by
    rw [hB]
    exact Finset.singleton_nonempty _
  have hKM := dalal_satisfiesKM (σ := Fin 2)
  have hSub := hKM.r1 (Finset.univ.filter fun I : Fin 2 → Bool => I 0 = true)
    (Finset.univ.filter fun I : Fin 2 → Bool => I 0 = false ∧ I 1 = true)
  have hNon := hKM.r3 (Finset.univ.filter fun I : Fin 2 → Bool => I 0 = true)
    (Finset.univ.filter fun I : Fin 2 → Bool => I 0 = false ∧ I 1 = true)
    hBNonempty
  rw [hB] at hSub hNon ⊢
  apply Finset.ext
  intro X
  constructor
  · intro hX
    exact hSub hX
  · intro hX
    rw [Finset.mem_singleton] at hX
    subst hX
    obtain ⟨Y, hY⟩ := hNon
    have hYSingle : Y ∈ ({fun a => decide (a = 1)} : Finset (Fin 2 → Bool)) :=
      hSub hY
    rw [Finset.mem_singleton] at hYSingle
    rw [hYSingle] at hY
    exact hY

/-- Revising by a sentence consistent with the knowledge base is expansion:
for consistent `A ∩ B`, every KM operator returns `A ∩ B` (postulate R2);
instantiated for Dalal on two atoms. -/
theorem dalal_expansion_two_atoms :
    dalalRev (σ := Fin 2)
        (Finset.univ.filter fun I => I 0 = true)
        (Finset.univ.filter fun I => I 1 = true)
      = (Finset.univ.filter fun I => I 0 = true) ∩
          (Finset.univ.filter fun I => I 1 = true) := by
  have hKM := dalal_satisfiesKM (σ := Fin 2)
  apply hKM.r2
  refine ⟨fun _ => true, ?_⟩
  rw [Finset.mem_inter]
  constructor
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩

/-- The empty model set is a legitimate knowledge base: Dalal revision of it
by a satisfiable sentence returns all of the sentence's models. -/
theorem dalal_empty_kb :
    dalalRev (σ := Fin 2) ∅ (Finset.univ.filter fun I => I 0 = true)
      = (Finset.univ.filter fun I => I 0 = true) := by
  have hKey : ∀ K : Interp (Fin 2),
      dalalKey (∅ : Finset (Interp (Fin 2))) K = 0 := by
    intro K
    unfold dalalKey
    split
    · next h =>
      exact absurd h Finset.not_nonempty_empty
    · rfl
  unfold dalalRev
  apply Finset.ext
  intro I
  rw [mem_minSet]
  constructor
  · intro h
    exact h.1
  · intro h
    constructor
    · exact h
    · intro J _ hStrict
      have hLe : dalalLe (∅ : Finset (Interp (Fin 2))) I J := by
        unfold dalalLe
        rw [hKey I, hKey J]
      exact hStrict.2 hLe

end Cslib.BeliefRevision.KMRevisionTest
