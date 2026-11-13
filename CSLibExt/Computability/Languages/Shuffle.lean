/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Shuffles of lists

`IsShuffle u v w` says that the list `w` interleaves `u` and `v`, keeping the order of each.
The relation is shared by the regular-language closure results in
`CSLibExt.Computability.Languages.RegularShuffle` and the register-trace projections in
`CSLibExt.Parallel.Interleaving`.
-/

@[expose] public section

namespace Cslib.Language

variable {α : Type*}

/-- `IsShuffle u v w`: the word `w` interleaves `u` and `v`. -/
inductive IsShuffle : List α → List α → List α → Prop
  | nil : IsShuffle [] [] []
  | left {u v w : List α} (a : α) : IsShuffle u v w → IsShuffle (a :: u) v (a :: w)
  | right {u v w : List α} (a : α) : IsShuffle u v w → IsShuffle u (a :: v) (a :: w)

theorem isShuffle_nil_iff {u v : List α} : IsShuffle u v [] ↔ u = [] ∧ v = [] := by
  constructor
  · rintro ⟨⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .nil

theorem isShuffle_cons_iff {u v w : List α} {a : α} :
    IsShuffle u v (a :: w) ↔
      (∃ u', u = a :: u' ∧ IsShuffle u' v w) ∨ ∃ v', v = a :: v' ∧ IsShuffle u v' w := by
  constructor
  · rintro (_ | ⟨_, h⟩ | ⟨_, h⟩)
    · exact .inl ⟨_, rfl, h⟩
    · exact .inr ⟨_, rfl, h⟩
  · rintro (⟨u', rfl, h⟩ | ⟨v', rfl, h⟩)
    exacts [.left a h, .right a h]

end Cslib.Language
