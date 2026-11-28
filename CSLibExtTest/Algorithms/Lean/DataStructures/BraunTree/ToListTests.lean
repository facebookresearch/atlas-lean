/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.ToList

/-!
# Braun-tree-to-list regression tests

Concrete `bleft` / `bright` / `bvalue` / `isNonLeaf` /
`list_fast_rec` / `list_fast` / `Tlist_fast_rec` cases, and
restatements of the unfolding equations, Theorem 11.8, the
`list_fast` corollary, and Theorem 11.9.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTreeToListTests

open BraunTree

/-- A complete tree with three elements. -/
private def t3 : Tree Nat := .Node (.Node .Leaf 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

/-- A Braun tree with four elements. -/
private def t4 : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

/-- A singleton tree. -/
private def t1 : Tree Nat := .Node .Leaf 1 .Leaf

/-- The empty tree, as a list element. -/
private def tLeaf : Tree Nat := .Leaf

example : bleft t3 = .Node .Leaf 2 .Leaf := by decide
example : bright t3 = .Node .Leaf 3 .Leaf := by decide
example : bvalue t3 = some 1 := by decide
example : bvalue (.Leaf : Tree Nat) = none := by decide
example : bleft (.Leaf : Tree Nat) = .Leaf := by decide
example : bright (.Leaf : Tree Nat) = .Leaf := by decide

example : isNonLeaf t3 = true := by decide
example : isNonLeaf (.Leaf : Tree Nat) = false := by decide

example : list_fast_rec [t3] = [1, 2, 3] := by decide
example : list_fast_rec [t4] = [1, 2, 3, 4] := by decide
example : list_fast_rec ([] : List (Tree Nat)) = [] := by decide
example : list_fast_rec [tLeaf] = [] := by decide
example : list_fast_rec [t3, t4] = [1, 1, 2, 2, 3, 3, 4] := by decide

example : list_fast t3 = [1, 2, 3] := by decide
example : list_fast t4 = [1, 2, 3, 4] := by decide
example : list_fast (.Leaf : Tree Nat) = [] := by decide

example : Tlist_fast_rec [t1] = 17 := by decide
example : Tlist_fast_rec ([] : List (Tree Nat)) = 2 := by decide
example : Tlist_fast_rec [tLeaf] = 3 := by decide

/-- `isNonLeaf` is the non-`Leaf` test. -/
example {α : Type u} {t : Tree α} : isNonLeaf t = true ↔ t ≠ .Leaf :=
  isNonLeaf_eq_true

/-- The one-step unfolding equation for `list_fast_rec`. -/
example {α : Type u} (ts : List (Tree α)) :
    list_fast_rec ts = if (ts.filter isNonLeaf).isEmpty then []
      else (ts.filter isNonLeaf).filterMap bvalue ++
        list_fast_rec ((ts.filter isNonLeaf).map bleft ++
          (ts.filter isNonLeaf).map bright) :=
  list_fast_rec_eq ts

/-- Theorem 11.8: breadth-first traversal of a level of Braun trees. -/
example {α : Type u} {k : ℕ} {xs : List α} {ts : List (Tree α)}
    (hlen : ts.length = 2 ^ k)
    (h : ∀ i (hi : i < ts.length), braun_list (ts[i]'hi) (take_nths i k xs)) :
    list_fast_rec ts = xs :=
  list_fast_rec_correct hlen h

/-- `list_fast` recovers the index-order list of a Braun tree. -/
example {α : Type u} {t : Tree α} (h : braun t) : list_fast t = list t :=
  list_fast_correct h

/-- The one-step unfolding equation for `Tlist_fast_rec`. -/
example {α : Type u} (ts : List (Tree α)) :
    Tlist_fast_rec ts = (ts.length + 1 + (if (ts.filter isNonLeaf).isEmpty then 0
      else 5 * ((ts.filter isNonLeaf).length + 1) +
        Tlist_fast_rec ((ts.filter isNonLeaf).map bleft
          ++ (ts.filter isNonLeaf).map bright))) + 1 :=
  Tlist_fast_rec_eq ts

/-- Theorem 11.9: `list_fast_rec` runs in linear time in the total size. -/
example {α : Type u} (ts : List (Tree α)) :
    Tlist_fast_rec ts ≤ 14 * (ts.map size).sum + ts.length + 2 :=
  Tlist_fast_rec_le ts

end Cslib.Algorithms.Lean.BraunTreeToListTests
