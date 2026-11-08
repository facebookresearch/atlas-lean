/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Union

/-! Ordinary downstream consumers of the three exact canonical LINK/UNION facts. -/

example (self : Batteries.UnionFind) (x y : Fin self.size)
    (yroot : self.parent y = y) (i : Nat) :
    (self.link x y yroot).rank i =
      if x.val ≠ y.val ∧ self.rank x = self.rank y ∧ y.val = i then
        self.rank y + 1 else self.rank i := by
  exact Batteries.UnionFind.rank_link self x y yroot i

example (self : Batteries.UnionFind) (x y : Fin self.size)
    (xroot : self.parent x = x) (yroot : self.parent y = y) (i : Nat) :
    (self.link x y yroot).rootD i =
      if self.rootD i = x.val ∨ self.rootD i = y.val then
        if self.rank y < self.rank x then x.val else y.val
      else self.rootD i := by
  exact Batteries.UnionFind.rootD_link_eq_ite self x y xroot yroot i

example (self : Batteries.UnionFind) (x y : Fin self.size) (i : Nat) :
    (self.union x y).rank i =
      if self.rootD x ≠ self.rootD y ∧
          self.rank (self.rootD x) = self.rank (self.rootD y) ∧ self.rootD y = i then
        self.rank (self.rootD y) + 1 else self.rank i := by
  exact Batteries.UnionFind.rank_union self x y i

example : IsEmpty (Fin Batteries.UnionFind.empty.size) := by
  change IsEmpty (Fin 0)
  infer_instance
