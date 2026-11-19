/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.OfList

/-!
# List-to-Braun-tree regression tests

Concrete `take_nths` / `nodes` / `brauns` cases, the `braun_list`
relation at a concrete tree, and restatements of the `take_nths`
identities, Lemma 11.4, Theorem 11.5, Corollary 11.6, and Lemma 11.7.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTreeOfListTests

open BraunTree

/-- A complete tree with three elements. -/
private def t3 : Tree Nat := .Node (.Node .Leaf 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

/-- A Braun tree with four elements. -/
private def t4 : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

example : take_nths 0 1 [1, 2, 3, 4, 5] = [1, 3, 5] := by decide
example : take_nths 1 1 [1, 2, 3, 4, 5] = [2, 4] := by decide
example : take_nths 0 2 [1, 2, 3, 4, 5, 6, 7] = [1, 5] := by decide
example : take_nths 2 1 [1, 2, 3, 4, 5] = [3, 5] := by decide
example : take_nths 3 2 [1, 2, 3, 4, 5, 6, 7] = [4] := by decide
example : take_nths 0 1 ([] : List Nat) = [] := by decide
example : take_nths 5 1 [1, 2, 3] = [] := by decide

example : brauns 0 [1, 2, 3] = [t3] := by simp [brauns, nodes, t3]
example : brauns 0 [1, 2, 3, 4] = [t4] := by simp [brauns, nodes, t4]
example : brauns 0 ([] : List Nat) = [] := by simp [brauns]
example : brauns 1 [1, 2, 3, 4] =
    [.Node (.Node .Leaf 3 .Leaf) 1 .Leaf,
      .Node (.Node .Leaf 4 .Leaf) 2 .Leaf] := by simp [brauns, nodes]
example : brauns1 [1, 2, 3] = t3 := by simp [brauns1, brauns, nodes, t3]
example : brauns1 [1, 2, 3, 4] = t4 := by simp [brauns1, brauns, nodes, t4]
example : brauns1 ([] : List Nat) = .Leaf := by simp [brauns1, brauns]

example : Ttake 2 [1, 2, 3] = 3 := by decide
example : Tdrop 5 [1, 2] = 3 := by decide
example : Tnodes [t3] [1, 2] [t3] = 3 := by decide

/-- The `braun_list` relation at a concrete tree. -/
example : braun_list t3 [1, 2, 3] :=
  braun_list_of_braun (by simp [braun, size, t3]) (by simp [list, splice, t3])

/-- The `braun_list` relation fails for the wrong list. -/
example : ¬ braun_list t3 [1, 2, 4] := by
  intro h
  have h2 := (braun_list_eq h).2
  rw [show list t3 = [1, 2, 3] from by simp [list, splice, t3]] at h2
  simp at h2

/-- (11.7): dropping then taking every nth is taking with a shift. -/
example {α : Type u} (i k : ℕ) (j : ℕ) (xs : List α) :
    take_nths i k (xs.drop j) = take_nths (i + j) k xs :=
  take_nths_drop i k j xs

/-- (11.8): stride-one taking is the identity. -/
example {α : Type u} (xs : List α) : take_nths 0 0 xs = xs :=
  take_nths_00 xs

/-- (11.9): splicing the even and odd subsequences recovers the list. -/
example {α : Type u} (xs : List α) :
    splice (take_nths 0 1 xs) (take_nths 1 1 xs) = xs :=
  take_nths_01_splice xs

/-- (11.11): taking is empty exactly past the end. -/
example {α : Type u} (i k : ℕ) (xs : List α) :
    take_nths i k xs = [] ↔ xs.length ≤ i :=
  take_nths_empty i k xs

/-- (11.14): the even and odd subsequences differ in length by at most one. -/
example {α : Type u} (xs : List α) :
    (take_nths 0 1 xs).length = (take_nths 1 1 xs).length ∨
      (take_nths 0 1 xs).length = (take_nths 1 1 xs).length + 1 :=
  length_take_nths xs

/-- (11.10): nested taking composes the indices. -/
example {α : Type u} (i m j n : ℕ) (xs : List α) :
    take_nths i m (take_nths j n xs) = take_nths (i * 2 ^ n + j) (m + n) xs :=
  take_nths_take_nths i m j n xs

/-- (11.13): taking from a splice recovers the two lists. -/
example {α : Type u} {xs ys : List α}
    (h : xs.length = ys.length ∨ xs.length = ys.length + 1) :
    take_nths 0 1 (splice xs ys) = xs ∧ take_nths 1 1 (splice xs ys) = ys :=
  take_nths_01_splice' h

/-- `braun_list` at a leaf is the empty list. -/
example {α : Type u} {xs : List α} :
    braun_list (.Leaf : Tree α) xs ↔ xs = [] :=
  braun_list_leaf

/-- Lemma 11.4: `braun_list` gives Braunness and the list. -/
example {α : Type u} {t : Tree α} {xs : List α} (h : braun_list t xs) :
    braun t ∧ xs = list t :=
  braun_list_eq h

/-- The converse of Lemma 11.4. -/
example {α : Type u} {t : Tree α} (h : braun t) {ys : List α}
    (hys : list t = ys) : braun_list t ys :=
  braun_list_of_braun h hys

/-- (11.15): `nodes` preserves the value-list length. -/
example {α : Type u} (ls : List (Tree α)) (xs : List α) (rs : List (Tree α)) :
    (nodes ls xs rs).length = xs.length :=
  length_nodes ls xs rs

/-- (11.16): the `i`-th `nodes` entry, via `getElem?`. -/
example {α : Type u} (ls : List (Tree α)) (xs : List α) (rs : List (Tree α))
    (i : ℕ) :
    (nodes ls xs rs)[i]? =
      (xs[i]?).map (fun x => Tree.Node (nthOrLeaf ls i) x (nthOrLeaf rs i)) :=
  nth_nodes ls xs rs i

/-- (11.17): `brauns` produces `min |xs| (2 ^ k)` trees. -/
example {α : Type u} (k : ℕ) (xs : List α) :
    (brauns k xs).length = min xs.length (2 ^ k) :=
  brauns_length k xs

/-- (11.12): the head of a `take_nths` is the `i`-th element. -/
example {α : Type u} {i k : ℕ} {xs : List α} (h : i < xs.length) :
    (take_nths i k xs).head? = xs[i]? :=
  head_take_nths h

/-- Theorem 11.5: every `brauns` tree is in the `braun_list` relation. -/
example {α : Type u} {xs : List α} {k : ℕ} {i : ℕ}
    (hi : i < min xs.length (2 ^ k)) :
    ∃ t, (brauns k xs)[i]? = some t ∧ braun_list t (take_nths i k xs) :=
  brauns_correct hi

/-- Corollary 11.6: `brauns1` builds the Braun tree for a list. -/
example {α : Type u} (xs : List α) :
    braun (brauns1 xs) ∧ list (brauns1 xs) = xs :=
  brauns1_correct xs

/-- Lemma 11.7: `brauns` runs in linear time. -/
example {α : Type u} (k : ℕ) (xs : List α) :
    Tbrauns k xs ≤ 9 * (xs.length + 1) :=
  Tbrauns_le k xs

end Cslib.Algorithms.Lean.BraunTreeOfListTests
