/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.CompletePartialOrder
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 37, Logic 39, Logic 40, Logic 41, Logic 51
-- Proposed path (advisory metadata only, not a review instruction).

open Set

-- Logic 37: Countable subsets of $\alpha$
def CountableSubsets.{u} (α : Type u) : Set (Set α) := {x | x.Countable}

theorem mem_countableSubsets.{u} {α : Type u} (x : Set α) :
    x ∈ CountableSubsets α ↔ x.Countable := Iff.rfl

theorem countableSubsets_iUnion.{u} {α : Type u} (f : ℕ → Set α)
    (hf : ∀ n, f n ∈ CountableSubsets α) : (⋃ n, f n) ∈ CountableSubsets α :=
  Set.countable_iUnion hf

theorem countableSubsets_eq_univ_iff.{u} (α : Type u) :
    CountableSubsets α = Set.univ ↔ Countable α := by
  constructor
  · intro h
    have hmem : (Set.univ : Set α) ∈ CountableSubsets α := by rw [h]; trivial
    exact Set.countable_univ_iff.mp hmem
  · intro h
    haveI := h
    ext x
    simp only [CountableSubsets, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact Set.to_countable x

-- Logic 39: Club in $[X]^\omega$
structure IsClubOmega {α : Type*} (C : Set (Set α)) : Prop where
  mem_countable : ∀ x ∈ C, x.Countable
  cofinal : ∀ x : Set α, x.Countable → ∃ y ∈ C, x ⊆ y
  closed : ∀ f : ℕ → Set α, (∀ n, f n ∈ C) → Monotone f → (⋃ n, f n) ∈ C

theorem IsClubOmega.nonempty.{u} {α : Type u} {C : Set (Set α)} (hC : IsClubOmega C) :
    C.Nonempty :=
  (hC.cofinal ∅ Set.countable_empty).imp fun _ hy => hy.1

theorem IsClubOmega.iUnion_countable.{u} {α : Type u} {C : Set (Set α)} (hC : IsClubOmega C)
    (f : ℕ → Set α) (hf : ∀ n, f n ∈ C) : (⋃ n, f n).Countable :=
  Set.countable_iUnion fun n => hC.mem_countable _ (hf n)

theorem isClubOmega_countableSubsets.{u} (α : Type u) : IsClubOmega (CountableSubsets α) where
  mem_countable := fun _ hx => hx
  cofinal := fun x hx => ⟨x, hx, subset_rfl⟩
  closed := fun _ hf _ => Set.countable_iUnion hf

theorem not_isClubOmega_empty.{u} {α : Type u} : ¬ IsClubOmega (∅ : Set (Set α)) :=
  fun h => h.nonempty.ne_empty rfl

-- Logic 40: Stationarity in $[X]^\omega$
def IsStationaryOmega {α : Type*} (S : Set (Set α)) : Prop :=
  ∀ ⦃C : Set (Set α)⦄, IsClubOmega C → (S ∩ C).Nonempty

theorem not_isStationaryOmega_empty.{u} {α : Type u} :
    ¬ IsStationaryOmega (∅ : Set (Set α)) := by
  intro h
  obtain ⟨x, hx, -⟩ := h (isClubOmega_countableSubsets α)
  exact hx

theorem isStationaryOmega_countableSubsets.{u} (α : Type u) :
    IsStationaryOmega (CountableSubsets α) :=
  fun _ hC => (hC.cofinal ∅ Set.countable_empty).imp
    fun y hy => ⟨hC.mem_countable y hy.1, hy.1⟩

theorem IsStationaryOmega.mono.{u} {α : Type u} {S T : Set (Set α)}
    (hS : IsStationaryOmega S) (hST : S ⊆ T) : IsStationaryOmega T :=
  fun _ hC => (hS hC).imp fun _ hx => ⟨hST hx.1, hx.2⟩

-- Logic 41: Closure points
def ClosurePoints {α : Type*} (F : Finset α → α) : Set (Set α) :=
  {x | x.Countable ∧ ∀ s : Finset α, ↑s ⊆ x → F s ∈ x}

theorem notMem_closurePoints_empty {α : Type*} (F : Finset α → α) :
    (∅ : Set α) ∉ ClosurePoints F :=
  fun h => h.2 ∅ (by simp)

theorem univ_mem_closurePoints {α : Type*} (hα : (Set.univ : Set α).Countable)
    (F : Finset α → α) : (Set.univ : Set α) ∈ ClosurePoints F :=
  ⟨hα, fun _ _ => Set.mem_univ _⟩

-- Logic 51: Closure Points Sequence
def ClosurePointsSeq {α : Type*} (F : ℕ → Finset α → α) : Set (Set α) :=
  {x | x.Countable ∧ ∀ (n : ℕ) (s : Finset α), ↑s ⊆ x → F n s ∈ x}

theorem notMem_closurePointsSeq_empty {α : Type*} (F : ℕ → Finset α → α) :
    (∅ : Set α) ∉ ClosurePointsSeq F :=
  fun h => h.2 0 ∅ (by simp)

theorem univ_mem_closurePointsSeq {α : Type*} (hα : (Set.univ : Set α).Countable)
    (F : ℕ → Finset α → α) : (Set.univ : Set α) ∈ ClosurePointsSeq F :=
  ⟨hα, fun _ _ _ => Set.mem_univ _⟩

end
