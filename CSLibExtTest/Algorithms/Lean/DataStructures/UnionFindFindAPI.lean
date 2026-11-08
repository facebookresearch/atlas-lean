/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Find

/-! Ordinary-import uses of all three canonical FIND facts. -/

open Batteries

open Classical in
example (self : UnionFind) (x : Fin self.size) (i : Nat) :
    (self.find x).1.parent i =
      if ∃ k : Nat, Nat.iterate self.parent k x.val = i then self.rootD x.val
      else self.parent i := self.find_parent_eq_ite_iterate x i

open Classical in
example (self : UnionFind) (x : Fin self.size) (i : Nat) (hi : i < self.size) :
    (self.find x).1.arr[i]'(by simpa using hi) =
      { parent := if ∃ k : Nat, Nat.iterate self.parent k x.val = i then
          self.rootD x.val else self.arr[i].parent
        rank := self.arr[i].rank } := self.getElem_find x i hi

example (self : UnionFind) (x : Fin self.size) :
    ∃ d : Nat,
      Nat.iterate self.parent d x.val = self.rootD x.val ∧
      (∀ k < d, Nat.iterate self.parent k x.val ≠ self.rootD x.val) ∧
      d < self.size := self.exists_first_iterate_rootD x

example (self : UnionFind) (x : Fin self.size) (i : Nat)
    (hoff : ∀ k : Nat, Nat.iterate self.parent k x.val ≠ i) :
    (self.find x).1.parent i = self.parent i := by
  rw [self.find_parent_eq_ite_iterate x i]
  exact ite_eq_right (by rintro ⟨k, hk⟩; exact hoff k hk)

example (self : UnionFind) (x : Fin self.size) (i : Nat) (hi : i < self.size) :
    ((self.find x).1.arr[i]'(by simpa using hi)).rank = self.arr[i].rank := by
  rw [self.getElem_find x i hi]

example : IsEmpty (Fin UnionFind.empty.size) := by
  change IsEmpty (Fin 0)
  infer_instance
