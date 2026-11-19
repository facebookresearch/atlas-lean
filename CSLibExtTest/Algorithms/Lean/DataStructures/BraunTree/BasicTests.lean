/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Basic

/-!
# Braun-tree shape regression tests

Concrete empty, singleton, and small trees for `size` / `height` /
`minHeight` / `inorder`, the `braun` / `acomplete` / `complete`
predicates, and the left-height `lh`, plus restatements of the
headline shape theorems. The non-Braun tree `lbad` violates the
size condition (`|l| = 3` against `|r| = 0`).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTreeBasicTests

open BraunTree

/-- The empty tree. -/
private def t0 : Tree Nat := .Leaf

/-- A singleton tree. -/
private def t1 : Tree Nat := .Node .Leaf 1 .Leaf

/-- A complete tree with three elements. -/
private def t3 : Tree Nat := .Node (.Node .Leaf 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

/-- A Braun, almost-complete, incomplete tree with four elements. -/
private def t4 : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

/-- An almost-complete, incomplete tree with five elements that is
not Braun (its left subtree is too large): a discriminator between
`braun` and `acomplete`. -/
private def t5 : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 (.Node .Leaf 5 .Leaf)) 1
    (.Node .Leaf 3 .Leaf)

/-- A complete tree with seven elements. -/
private def t7 : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 (.Node .Leaf 5 .Leaf)) 1
    (.Node (.Node .Leaf 6 .Leaf) 3 (.Node .Leaf 7 .Leaf))

/-- Not Braun: the left subtree has three elements, the right none. -/
private def lbad : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 .Leaf) 1 .Leaf

example : size t0 = 0 := by decide
example : size t1 = 1 := by decide
example : size t3 = 3 := by decide
example : size t4 = 4 := by decide
example : size t5 = 5 := by decide
example : size t7 = 7 := by decide
example : size lbad = 3 := by decide

example : height t0 = 0 := by decide
example : height t1 = 1 := by decide
example : height t3 = 2 := by decide
example : height t4 = 3 := by decide
example : height t5 = 3 := by decide
example : height t7 = 3 := by decide
example : height lbad = 3 := by decide

example : minHeight t0 = 0 := by decide
example : minHeight t1 = 1 := by decide
example : minHeight t3 = 2 := by decide
example : minHeight t4 = 2 := by decide
example : minHeight t5 = 2 := by decide
example : minHeight t7 = 3 := by decide
example : minHeight lbad = 1 := by decide

example : inorder t0 = [] := by decide
example : inorder t1 = [1] := by decide
example : inorder t3 = [2, 1, 3] := by decide
example : inorder t4 = [4, 2, 1, 3] := by decide
example : inorder t5 = [4, 2, 5, 1, 3] := by decide
example : inorder t7 = [4, 2, 5, 1, 6, 3, 7] := by decide
example : inorder lbad = [4, 2, 1] := by decide

example : braun t0 := by simp [braun, t0]
example : braun t1 := by simp [braun, size, t1]
example : braun t3 := by simp [braun, size, t3]
example : braun t4 := by simp [braun, size, t4]
example : ¬ braun t5 := by simp [braun, size, t5]
example : braun t7 := by simp [braun, size, t7]
example : ¬ braun lbad := by simp [braun, size, lbad]

example : acomplete t0 := by simp [acomplete, t0]
example : acomplete t1 := by simp [acomplete, height, minHeight, t1]
example : acomplete t3 := by simp [acomplete, height, minHeight, t3]
example : acomplete t4 := by simp [acomplete, height, minHeight, t4]
example : acomplete t5 := by simp [acomplete, height, minHeight, t5]
example : acomplete t7 := by simp [acomplete, height, minHeight, t7]
example : ¬ acomplete lbad := by simp [acomplete, height, minHeight, lbad]

example : complete t0 := by simp [complete, t0]
example : complete t1 := by simp [complete, height, t1]
example : complete t3 := by simp [complete, height, t3]
example : ¬ complete t4 := by simp [complete, height, t4]
example : ¬ complete t5 := by simp [complete, height, t5]
example : complete t7 := by simp [complete, height, t7]
example : ¬ complete lbad := by simp [complete, height, lbad]

example : lh t3 = 2 := by decide
example : lh t4 = 3 := by decide
example : lh t7 = 3 := by decide

/-- Lemma 11.2: every Braun tree is almost complete. -/
example {α : Type u} {t : Tree α} (h : braun t) : acomplete t :=
  braun_acomplete h

/-- The book's `acomplete` definition, as an iff. -/
example {α : Type u} {t : Tree α} :
    acomplete t ↔ height t ≤ minHeight t + 1 :=
  acomplete_iff

/-- Lemma 4.7: a nonempty almost-complete tree has logarithmic height. -/
example {α : Type u} {t : Tree α} (h : acomplete t) (hne : t ≠ .Leaf) :
    height t = Nat.log2 (size t) + 1 :=
  acomplete_height_log h hne

/-- Lemma 4.8: the minimum height of an almost-complete tree. -/
example {α : Type u} {t : Tree α} (h : acomplete t) :
    minHeight t = Nat.log2 (size t + 1) :=
  acomplete_minHeight_log h

/-- Exercise 11.1: a nonempty Braun tree has logarithmic height. -/
example {α : Type u} {t : Tree α} (h : braun t) (hne : t ≠ .Leaf) :
    height t = Nat.log2 (size t) + 1 :=
  braun_height_log h hne

/-- A Braun tree's left height is its height. -/
example {α : Type u} {t : Tree α} (h : braun t) : lh t = height t :=
  braun_lh_eq_height h

/-- Lemma 4.2: a complete tree has `2 ^ h - 1` elements. -/
example {α : Type u} {t : Tree α} (h : complete t) :
    size t + 1 = 2 ^ height t :=
  complete_size h

/-- Corollary 4.5: completeness is the size equation. -/
example {α : Type u} {t : Tree α} :
    complete t ↔ size t + 1 = 2 ^ height t :=
  complete_iff_size

/-- Lemma 4.6: an almost-complete tree has minimal height. -/
example {α : Type u} {s t : Tree α} (hs : acomplete s)
    (h : size s ≤ size t) : height s ≤ height t :=
  acomplete_height_optimal hs h

/-- Exercise 4.8: almost-completeness at a node. -/
example {α : Type u} {l r : Tree α} {x : α} :
    acomplete (.Node l x r) ↔ acomplete l ∧ acomplete r ∧
      ((height l = height r) ∨
        (height l = height r + 1 ∧ complete r) ∨
        (height r = height l + 1 ∧ complete l)) :=
  acomplete_node_iff

/-- Braunness at a node is the size condition plus Braun children. -/
example {α : Type u} {l r : Tree α} {x : α} :
    braun (.Node l x r) ↔
      (size l = size r ∨ size l = size r + 1) ∧ braun l ∧ braun r :=
  braun_node

/-- Completeness at a node is equal heights plus complete children. -/
example {α : Type u} {l r : Tree α} {x : α} :
    complete (.Node l x r) ↔
      height l = height r ∧ complete l ∧ complete r :=
  complete_node

/-- A perfect tree has `2 ^ h - 1` elements. -/
example {α : Type u} {t : Tree α} (h : minHeight t = height t) :
    size t + 1 = 2 ^ height t :=
  perfect_size h

/-- A nonempty almost-complete tree has at least `2 ^ (h - 1)` elements. -/
example {α : Type u} {t : Tree α} (h : acomplete t) (hne : t ≠ .Leaf) :
    2 ^ (height t - 1) ≤ size t :=
  acomplete_size_sharp h hne

end Cslib.Algorithms.Lean.BraunTreeBasicTests
