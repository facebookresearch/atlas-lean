/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.StarFreeHeight

/-! # Tests for the local star-free and generalized-height bridge -/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe v

example {α : Type v} {L : Language α} (h : IsStarFree L) : HasGenHeightLe L 0 :=
  h.hasGenHeightLe_zero

example : HasGenHeightLe (0 : Language PEmpty) 0 :=
  IsStarFree.empty.hasGenHeightLe_zero

example : HasGenHeightLe ((0 : Language PEmpty)ᶜ) 0 :=
  (IsStarFree.compl IsStarFree.empty).hasGenHeightLe_zero

example : HasGenHeightLe (({[true]} : Language Bool) + {[false]}) 0 :=
  (IsStarFree.union (IsStarFree.singleton true) (IsStarFree.singleton false)).hasGenHeightLe_zero

example : HasGenHeightLe (({[true]} : Language Bool) * {[false]}) 0 :=
  (IsStarFree.concat (IsStarFree.singleton true) (IsStarFree.singleton false)).hasGenHeightLe_zero

example {α : Type v} [Infinite α] : ¬ IsStarFree (1 : Language α) :=
  not_isStarFree_one

example : HasGenHeightLe (1 : Language ℕ) 0 ∧ ¬ IsStarFree (1 : Language ℕ) :=
  ⟨hasGenHeightLe_zero_one, not_isStarFree_one⟩

example {α : Type v} [Infinite α] :
    ¬ (∀ L : Language α, HasGenHeightLe L 0 → IsStarFree L) := by
  intro h
  exact not_isStarFree_one (h 1 hasGenHeightLe_zero_one)

#print axioms not_isStarFree_one
#print axioms IsStarFree.hasGenHeightLe_zero

end Cslib.Language
