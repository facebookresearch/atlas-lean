/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Preference.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Economics

namespace MathlibExtTest.Economics.Preference.Basic

namespace PreferenceExamples

/-- Three alternatives ranked by the scores `1, 1, 0`: alternatives `0` and `1` tie at the top. -/
def tiePref : Preference (Fin 3) where
  R x y := (![1, 1, 0] : Fin 3 → ℕ) y ≤ (![1, 1, 0] : Fin 3 → ℕ) x
  complete := by
    intro x y
    exact le_total _ _
  trans := by
    intro x y z h1 h2
    exact le_trans h2 h1

theorem tiePref_choice_nonempty : (tiePref.choice (Set.univ : Set (Fin 3))).Nonempty := by
  exact Preference.choice_nonempty tiePref Set.finite_univ Set.univ_nonempty

theorem tiePref_choice_univ : tiePref.choice (Set.univ : Set (Fin 3)) = {0, 1} := by
  ext x
  simp only [Preference.choice, Set.mem_ofPred_eq, Set.mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  fin_cases x <;> simp [tiePref] <;> decide

theorem choice_singleton {α : Type*} (P : Preference α) (x : α) : P.choice {x} = {x} := by
  ext y
  simp only [Preference.choice, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl, _⟩
    rfl
  · rintro rfl
    refine ⟨rfl, fun z hz => ?_⟩
    subst hz
    rcases P.complete _ _ with h | h <;> exact h

/-- A complete but cyclic (intransitive) relation on three alternatives: `0 ≻ 1 ≻ 2 ≻ 0`. -/
def cyclic (x y : Fin 3) : Prop :=
  x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 0)

theorem cyclic_complete (x y : Fin 3) : cyclic x y ∨ cyclic y x := by
  fin_cases x <;> fin_cases y <;> simp only [cyclic] <;> decide

theorem cyclic_not_transitive :
    ¬ (∀ x y z, cyclic x y → cyclic y z → cyclic x z) := by
  intro h
  have h02 := h 0 1 2 (by simp [cyclic]) (by simp [cyclic])
  simp [cyclic] at h02

/-- Completeness suffices even though the relation is intransitive. -/
theorem cyclic_maximal_eq_choice (B : Set (Fin 3)) :
    PreferenceRelation.maximal cyclic B = PreferenceRelation.choice cyclic B :=
  PreferenceRelation.maximal_eq_choice cyclic cyclic_complete B

/-- On a proper menu the cyclic relation has a nonempty choice set. -/
theorem cyclic_maximal_pair :
    PreferenceRelation.maximal cyclic ({0, 1} : Set (Fin 3)) = {0} := by
  rw [cyclic_maximal_eq_choice]
  ext x
  fin_cases x <;> simp [PreferenceRelation.choice, cyclic]

theorem cyclic_no_greatest : ¬ ∃ x : Fin 3, ∀ y, cyclic x y := by
  rintro ⟨x, hx⟩
  fin_cases x
  · exact absurd (hx 2) (by simp [cyclic])
  · exact absurd (hx 0) (by simp [cyclic])
  · exact absurd (hx 1) (by simp [cyclic])

end PreferenceExamples

end MathlibExtTest.Economics.Preference.Basic
