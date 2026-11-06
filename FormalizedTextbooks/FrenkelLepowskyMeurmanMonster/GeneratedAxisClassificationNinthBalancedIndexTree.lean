/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-! Balanced index lookup agrees with the complete original list, including absent indices. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A finite value tree with the size of its left subtree stored at each branch. -/
inductive GeneratedNinthBalancedIndexTree where
  | empty
  | leaf (value : ℕ)
  | branch (leftSize : ℕ) (left right : GeneratedNinthBalancedIndexTree)
  deriving DecidableEq

namespace GeneratedNinthBalancedIndexTree

/-- The complete ordered list represented by the tree. -/
def toList : GeneratedNinthBalancedIndexTree → List ℕ
  | empty => []
  | leaf v => [v]
  | branch _ l r => l.toList ++ r.toList

/-- Every stored left-subtree size is the actual list length. -/
def Valid : GeneratedNinthBalancedIndexTree → Prop
  | empty => True
  | leaf _ => True
  | branch s l r => l.Valid ∧ r.Valid ∧ s = l.toList.length

/-- The metadata predicate has a direct finite recursive decision procedure. -/
def validDecidable : (t : GeneratedNinthBalancedIndexTree) → Decidable t.Valid
  | empty => isTrue trivial
  | leaf _ => isTrue trivial
  | branch _ l r =>
      have : Decidable l.Valid := validDecidable l
      have : Decidable r.Valid := validDecidable r
      inferInstanceAs (Decidable (l.Valid ∧ r.Valid ∧ _))

instance (t : GeneratedNinthBalancedIndexTree) : Decidable t.Valid := validDecidable t

/-- Lookup uses the stored size and returns zero at every absent index. -/
def lookup : GeneratedNinthBalancedIndexTree → ℕ → ℕ
  | empty, _ => 0
  | leaf v, n => if n = 0 then v else 0
  | branch s l r, n => if n < s then l.lookup n else r.lookup (n - s)

/-- Every valid tree gives exactly the ordinary ordered-list lookup for every natural index. -/
theorem lookup_eq_list (t : GeneratedNinthBalancedIndexTree) (h : t.Valid) (n : ℕ) :
    t.lookup n = t.toList[n]?.getD 0 := by
  induction t generalizing n with
  | empty => rfl
  | leaf v => cases n <;> rfl
  | branch s l r ihl ihr =>
      rcases h with ⟨hl, hr, hs⟩
      by_cases hn : n < s
      · simp only [lookup, hn, ite_true, toList]
        rw [List.getElem?_append_left (by omega)]
        exact ihl hl n
      · simp only [lookup, hn, ite_false, toList]
        rw [List.getElem?_append_right (by omega), ← hs]
        exact ihr hr (n - s)

end GeneratedNinthBalancedIndexTree
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
