/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.GroupAction.StabilizerDivides
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

/-!
# Examples for the stabilizer-divides-cardinality lemma

Exercises `Subgroup.card_stabilizer_dvd_card` on permutations of a three-element
set: the trivial subgroup stabilizes the whole group, the whole group stabilizes
itself, and a subgroup stabilizes each of its left-multiplication orbits.
-/

/-- The trivial subgroup stabilizes every finite set; here `|⊥| = 1` divides `6`. -/
example : Nat.card (⊥ : Subgroup (Equiv.Perm (Fin 3))) ∣
    (Finset.univ : Finset (Equiv.Perm (Fin 3))).card := by
  have h := Subgroup.card_stabilizer_dvd_card (⊥ : Subgroup (Equiv.Perm (Fin 3)))
    Finset.univ (fun h hh u _ => Finset.mem_univ _)
  exact h

/-- The whole group stabilizes itself; here `|⊤| = 6` divides `6`. -/
example : Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 3))) ∣
    (Finset.univ : Finset (Equiv.Perm (Fin 3))).card := by
  have h := Subgroup.card_stabilizer_dvd_card (⊤ : Subgroup (Equiv.Perm (Fin 3)))
    Finset.univ (fun h _ u _ => Finset.mem_univ _)
  exact h

/-- A subgroup stabilizes each of its left-multiplication orbits, so its order
divides the orbit size (indeed the orbit has exactly `|H|` elements). -/
example {G : Type*} [Group G] [Fintype G] [DecidableEq G] (H : Subgroup G) [Fintype H]
    (u₀ : G) :
    Nat.card H ∣ (Finset.univ.image (fun h : H => (h : G) * u₀)).card := by
  apply Subgroup.card_stabilizer_dvd_card H
  intro h hh u hu
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu ⊢
  obtain ⟨⟨h', hh'⟩, rfl⟩ := hu
  exact ⟨⟨h * h', H.mul_mem hh hh'⟩, by simp [mul_assoc]⟩
