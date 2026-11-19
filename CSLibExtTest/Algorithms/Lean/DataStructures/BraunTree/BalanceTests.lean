/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Balance

/-!
# `bal` regression tests

Concrete `bal` / `bal_list` / `balance_list` / `bal_tree` /
`balance_tree` cases, and restatements of the `bal` specification
(Lemma 4.9), Exercise 11.4, Corollary 4.12, and Exercise 4.9.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTreeBalanceTests

open BraunTree

/-- A complete tree with three elements. -/
private def t3 : Tree Nat := .Node (.Node .Leaf 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

example : bal 0 [1, 2, 3] = (.Leaf, [1, 2, 3]) := by simp [bal]
example : bal 1 [1, 2, 3] = (.Node .Leaf 1 .Leaf, [2, 3]) := by simp [bal]
example : bal 2 [1, 2, 3] = (.Node (.Node .Leaf 1 .Leaf) 2 .Leaf, [3]) :=
  by simp [bal]
example : bal 3 [1, 2, 3] =
    (.Node (.Node .Leaf 1 .Leaf) 2 (.Node .Leaf 3 .Leaf), []) := by simp [bal]
example : bal 0 ([] : List Nat) = (.Leaf, []) := by simp [bal]
example : bal 4 [1, 2, 3, 4] =
    (.Node (.Node (.Node .Leaf 1 .Leaf) 2 .Leaf) 3 (.Node .Leaf 4 .Leaf),
      []) := by simp [bal]

example : bal_list 2 [1, 2, 3] = .Node (.Node .Leaf 1 .Leaf) 2 .Leaf := by
  simp [bal_list, bal]
example : balance_list [1, 2, 3] =
    .Node (.Node .Leaf 1 .Leaf) 2 (.Node .Leaf 3 .Leaf) := by
  simp [balance_list, bal_list, bal]
example : bal_tree 2 t3 = .Node (.Node .Leaf 2 .Leaf) 1 .Leaf := by
  simp [bal_tree, bal_list, bal, inorder, t3]
example : balance_tree t3 = t3 := by
  simp [balance_tree, bal_tree, bal_list, bal, inorder, size, t3]

/-- Lemma 4.9: `bal` returns a Braun tree with the right inorder,
remainder, and size. -/
example {α : Type u} {n : ℕ} {xs : List α} (hn : n ≤ xs.length)
    {t : Tree α} {zs : List α} (h : bal n xs = (t, zs)) :
    braun t ∧ inorder t = List.take n xs ∧ zs = List.drop n xs ∧ size t = n :=
  bal_spec hn h

/-- `bal` returns a Braun tree (Exercise 11.4). -/
example {α : Type u} {n : ℕ} {xs : List α} (hn : n ≤ xs.length)
    {t : Tree α} {zs : List α} (h : bal n xs = (t, zs)) : braun t :=
  bal_braun hn h

/-- Corollary 4.12: `bal` returns an almost-complete tree. -/
example {α : Type u} {n : ℕ} {xs : List α} (hn : n ≤ xs.length)
    {t : Tree α} {zs : List α} (h : bal n xs = (t, zs)) : acomplete t :=
  bal_acomplete hn h

/-- `bal_list` has the first-`n`-elements inorder. -/
example {α : Type u} {n : ℕ} {xs : List α} (hn : n ≤ xs.length) :
    inorder (bal_list n xs) = List.take n xs :=
  bal_list_inorder hn

/-- `bal_list` produces a Braun tree. -/
example {α : Type u} {n : ℕ} {xs : List α} (hn : n ≤ xs.length) :
    braun (bal_list n xs) :=
  bal_list_braun hn

/-- `balance_list` recovers the list by inorder. -/
example {α : Type u} {xs : List α} : inorder (balance_list xs) = xs :=
  balance_list_inorder

/-- `balance_list` produces a Braun tree. -/
example {α : Type u} {xs : List α} : braun (balance_list xs) :=
  balance_list_braun

/-- `bal_tree` has the first-`n`-elements inorder. -/
example {α : Type u} {n : ℕ} {t : Tree α} (hn : n ≤ size t) :
    inorder (bal_tree n t) = List.take n (inorder t) :=
  bal_tree_inorder hn

/-- `balance_tree` preserves the inorder. -/
example {α : Type u} {t : Tree α} : inorder (balance_tree t) = inorder t :=
  balance_tree_inorder

/-- Exercise 4.9: `bal` runs in linear time. -/
example {α : Type u} (n : ℕ) (xs : List α) : Tbal n xs ≤ 4 * n + 1 :=
  Tbal_le n xs

end Cslib.Algorithms.Lean.BraunTreeBalanceTests
