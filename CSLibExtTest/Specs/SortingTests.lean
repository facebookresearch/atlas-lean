/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Specs.Sorting

open CSLibExt.Specs.Sorting

universe u

-- The relation requires only LE, not decidability or any order laws.
example {α : Type u} [LE α] (xs ys : List α) :
    SortingSpec xs ys ↔ List.Perm ys xs ∧ List.Pairwise (· ≤ ·) ys :=
  Iff.rfl

example {α : Type u} [LE α] (xs : List α) :
    SortedProp xs ↔ List.Pairwise (· ≤ ·) xs := Iff.rfl

example {α : Type u} [LE α] : SortingSpec ([] : List α) [] :=
  ⟨List.Perm.refl _, List.Pairwise.nil⟩

example {α : Type u} [LE α] (x : α) : SortingSpec [x] [x] :=
  ⟨List.Perm.refl _, List.Pairwise.cons (by simp) List.Pairwise.nil⟩

example : SortingSpec [2, 1] [1, 2] := by
  unfold SortingSpec SortedProp
  decide

example : SortingSpec ([0, -2, 0, -1] : List Int) [-2, -1, 0, 0] := by
  unfold SortingSpec SortedProp
  decide

-- Sortedness alone does not preserve duplicate multiplicities.
example : ¬ SortingSpec [1, 1, 2] [1, 2] := by
  unfold SortingSpec SortedProp
  decide

-- Permutation alone does not ensure sortedness.
example : ¬ SortingSpec [1, 2] [2, 1] := by
  unfold SortingSpec SortedProp
  decide

example : ¬ SortedProp ([2, 1] : List Nat) := by
  unfold SortedProp
  decide

-- This carrier has no order laws, and occupies Type 1.
example :
    letI : LE (ULift.{1} Unit) := ⟨fun _ _ => False⟩
    SortingSpec ([⟨()⟩] : List (ULift.{1} Unit)) [⟨()⟩] := by
  exact ⟨List.Perm.refl _,
    List.Pairwise.cons (by simp) List.Pairwise.nil⟩

example :
    letI : LE Unit := ⟨fun _ _ => False⟩
    ¬ SortingSpec [(), ()] [(), ()] := by
  intro h
  exact (List.pairwise_cons.mp h.2).1 () (by simp)
