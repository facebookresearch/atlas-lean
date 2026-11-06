/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A verified sparse coefficient lookup avoids enumerating the ambient spin space. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactInverseSparse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A sparse vector can be evaluated by an inverse label lookup on its proved support. -/
theorem monsterNortonSparseLookup_eval {α β : Type*} [Fintype α] [DecidableEq β]
    (label : α → β) (lookup : β → α) (support : β → Prop) [DecidablePred support]
    (hl : ∀ a, lookup (label a) = a) (hs : ∀ a, support (label a))
    (hk : ∀ n, support n → label (lookup n) = n) (c : α → ℤ) (n : β) :
    (∑ a : α, c a • (Pi.single (label a) 1 : β → ℤ)) n =
      if support n then c (lookup n) else 0 := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hn : support n
  · have he (a : α) : n = label a ↔ a = lookup n := by
      constructor
      · intro h
        have hh := congrArg lookup h
        rw [hl] at hh
        exact hh.symm
      · intro h
        rw [h, hk n hn]
    simp [Pi.single_apply, he, hn, mul_ite]
  · have he (a : α) : n ≠ label a := by
      intro h
      exact hn (h ▸ hs a)
    simp [he, hn]

/-- The sparse sum is exactly the supported coefficient lookup as an entire integer vector. -/
theorem monsterNortonSparseLookup_eq {α β : Type*} [Fintype α] [DecidableEq β]
    (label : α → β) (lookup : β → α) (support : β → Prop) [DecidablePred support]
    (hl : ∀ a, lookup (label a) = a) (hs : ∀ a, support (label a))
    (hk : ∀ n, support n → label (lookup n) = n) (c : α → ℤ) :
    (∑ a : α, c a • (Pi.single (label a) 1 : β → ℤ)) =
      fun n => if support n then c (lookup n) else 0 := by
  funext n
  exact monsterNortonSparseLookup_eval label lookup support hl hs hk c n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
