/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Code.Inequalities.ReimerSwapInjClose
import Mathlib.Combinatorics.Hall.Basic

open Finset Function
open StatMech ConfigSpace

namespace StatMech.Walls




















theorem rc2_hall_available {α : Type*} {β : Type*} [Fintype β]
    (r : α → β → Prop) [DecidableRel r]
    (hHall : ∀ A : Finset α, #A ≤ #{b | ∃ a ∈ A, r a b}) :
    ∃ f : α → β, Injective f ∧ ∀ x, r x (f x) :=
  (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hHall





theorem rc2_hall_iff {α : Type*} {β : Type*} [Fintype β]
    (r : α → β → Prop) [DecidableRel r] :
    (∀ A : Finset α, #A ≤ #{b | ∃ a ∈ A, r a b}) ↔
      ∃ f : α → β, Injective f ∧ ∀ x, r x (f x) :=
  Fintype.all_card_le_filter_rel_iff_exists_injective r





theorem rc2_hall_necessary {α : Type*} {β : Type*} [Fintype β]
    (r : α → β → Prop) [DecidableRel r]
    (h : ∃ f : α → β, Injective f ∧ ∀ x, r x (f x)) :
    ∀ A : Finset α, #A ≤ #{b | ∃ a ∈ A, r a b} :=
  (Fintype.all_card_le_filter_rel_iff_exists_injective r).mpr h









variable {α : Type*} [Fintype α] [DecidableEq α]







theorem rc2_hall_for_swapInjection (A B : Set (ConfigSpace α))
    (r : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} →
         (ConfigSpace α × ConfigSpace α) → Prop) [DecidableRel r]
    (hHall : ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α //
          p.1 ∈ disjointOccurrence A B},
        #Aset ≤ #{b | ∃ a ∈ Aset, r a b}) :
    ∃ f : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} →
            (ConfigSpace α × ConfigSpace α),
        Injective f ∧ ∀ x, r x (f x) :=
  rc2_hall_available r hHall







set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in




theorem rc2_hall_available_nonvacuous {β : Type*} [Fintype β] [DecidableEq β] :
    ∃ f : β → β, Injective f ∧ ∀ x, (· = ·) x (f x) :=
  rc2_hall_available (· = ·) (by
    intro A
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hx, rfl⟩)

end StatMech.Walls
