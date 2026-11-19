/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Size

/-!
# Fast-size and initialisation regression tests

Concrete `diff` / `size_fast` / `braun_of` / `braun_of_naive` cases,
and restatements of Lemma 11.3, the `braun_of` specs, Exercise 11.7,
and Exercise 11.8.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTreeSizeTests

open BraunTree

/-- A complete tree with three elements. -/
private def t3 : Tree Nat := .Node (.Node .Leaf 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

/-- A Braun tree with four elements. -/
private def t4 : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

example : size_fast t3 = 3 := by decide
example : size_fast t4 = 4 := by decide
example : size_fast (.Leaf : Tree Nat) = 0 := by decide

example : diff t3 3 = 0 := by decide
example : diff t3 2 = 1 := by decide
example : diff t3 1 = 1 := by decide
example : diff t3 0 = 1 := by decide
example : diff (.Leaf : Tree Nat) 5 = 0 := by decide

example : braun_of 0 0 = (.Leaf : Tree Nat) := by simp [braun_of, braun2_of]
example : braun_of 0 1 = .Node .Leaf 0 .Leaf := by simp [braun_of, braun2_of]
example : braun_of 0 3 =
    .Node (.Node .Leaf 0 .Leaf) 0 (.Node .Leaf 0 .Leaf) :=
  by simp [braun_of, braun2_of]
example : list (braun_of 0 5) = [0, 0, 0, 0, 0] := by
  rw [braun_of_list]; rfl

example : braun_of_naive 0 0 = (.Leaf : Tree Nat) := by simp [braun_of_naive]
example : list (braun_of_naive 0 1) = [0] := by
  rw [braun_of_naive_list]; rfl
example : list (braun_of_naive 0 3) = [0, 0, 0] := by
  rw [braun_of_naive_list]; rfl

/-- Lemma 11.3: `diff` measures the missing part of the size. -/
example {α : Type u} {t : Tree α} (n : ℕ) (h : braun t)
    (hs : size t = n ∨ size t = n + 1) : diff t n = size t - n :=
  diff_spec n h hs

/-- Lemma 11.3: `size_fast` is the size on Braun trees. -/
example {α : Type u} {t : Tree α} (h : braun t) : size_fast t = size t :=
  size_fast_correct h

/-- `braun2_of`: sizes, Braunness, and lists of both trees. -/
example {α : Type u} (x : α) (n : ℕ) :
    size (braun2_of x n).1 = n ∧ size (braun2_of x n).2 = n + 1 ∧
      braun (braun2_of x n).1 ∧ braun (braun2_of x n).2 ∧
      list (braun2_of x n).1 = List.replicate n x ∧
      list (braun2_of x n).2 = List.replicate (n + 1) x :=
  braun2_of_spec x n

/-- `braun_of` lists the constant value. -/
example {α : Type u} (x : α) (n : ℕ) :
    list (braun_of x n) = List.replicate n x :=
  braun_of_list x n

/-- `braun_of` produces a Braun tree. -/
example {α : Type u} (x : α) (n : ℕ) : braun (braun_of x n) :=
  braun_of_braun x n

/-- `braun_of` produces a tree of the right size. -/
example {α : Type u} (x : α) (n : ℕ) : size (braun_of x n) = n :=
  braun_of_size x n

/-- Exercise 11.7: the naive construction lists the constant value. -/
example {α : Type u} (x : α) (n : ℕ) :
    list (braun_of_naive x n) = List.replicate n x :=
  braun_of_naive_list x n

/-- `Tdiff` descends along one path. -/
example {α : Type u} (t : Tree α) (n : ℕ) : Tdiff t n ≤ height t :=
  Tdiff_le_height t n

/-- Exercise 11.8: `Tsize_fast` is quadratic in the height. -/
example {α : Type u} (t : Tree α) : Tsize_fast t ≤ (height t) ^ 2 :=
  size_fast_time_le t

end Cslib.Algorithms.Lean.BraunTreeSizeTests
