/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Option.Basic

/-! A sparse lookup returns only an original entry having the requested address. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A finite source search tree retains each original entry index at its node. -/
inductive GeneratedNinthIncomingTree (ι : Type*) where
  /-- An empty source subtree. -/
  | empty : GeneratedNinthIncomingTree ι
  /-- One original source index and its two source subtrees. -/
  | node (i : ι) (left right : GeneratedNinthIncomingTree ι) : GeneratedNinthIncomingTree ι

/-- Exact search by the original numerical address of an entry. -/
def GeneratedNinthIncomingTree.lookup {ι : Type*} (key : ι → Nat)
    (t : GeneratedNinthIncomingTree ι) (q : Nat) : Option ι :=
  match t with
  | .empty => none
  | .node i l r =>
    if q = key i then some i else if q < key i then l.lookup key q else r.lookup key q

/-- Every returned original entry has exactly the requested source address. -/
theorem GeneratedNinthIncomingTree.lookup_sound {ι : Type*} (key : ι → Nat)
    (t : GeneratedNinthIncomingTree ι) (q : Nat) (i : ι)
    (h : t.lookup key q = some i) : key i = q := by
  induction t with
  | empty => simp [lookup] at h
  | node j l r ihl ihr =>
    by_cases hq : q = key j
    · have hj : j = i := by simpa only [lookup, hq, ite_true, Option.some.injEq] using h
      rw [← hj]
      exact hq.symm
    · by_cases hl : q < key j
      · apply ihl
        simpa only [lookup, hq, ite_false, hl, ite_true] using h
      · apply ihr
        simpa only [lookup, hq, ite_false, hl] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
