/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Array

/-!
# Array-via-Braun-tree regression tests

Concrete `list` / `lookup1` / `update1` / `ofList` / `Array` cases
(including the index-order subtlety at positions 5–7, and the
`ofList` result shape `o5`, which differs from the hand-built `t5`
in `BasicTests`), trie lookup / update (Exercise 11.5), and
restatements of the correctness specs and running-time bounds.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTreeArrayTests

open BraunTree

/-- A complete tree with three elements. -/
private def t3 : Tree Nat := .Node (.Node .Leaf 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

/-- A Braun tree with four elements. -/
private def t4 : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

/-- A complete tree with seven elements. -/
private def t7 : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 (.Node .Leaf 5 .Leaf)) 1
    (.Node (.Node .Leaf 6 .Leaf) 3 (.Node .Leaf 7 .Leaf))

/-- What `ofList [1, 2, 3, 4, 5]` produces (successive appends). -/
private def o5 : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 .Leaf) 1
    (.Node (.Node .Leaf 5 .Leaf) 3 .Leaf)

example : list t3 = [1, 2, 3] := by simp [list, splice, t3]
example : list t4 = [1, 2, 3, 4] := by simp [list, splice, t4]
example : list t7 = [1, 2, 3, 4, 6, 5, 7] := by simp [list, splice, t7]
example : list o5 = [1, 2, 3, 4, 5] := by simp [list, splice, o5]
example : list (.Leaf : Tree Nat) = [] := by decide

example : lookup1 1 t3 = some 1 := by decide
example : lookup1 2 t3 = some 2 := by decide
example : lookup1 3 t3 = some 3 := by decide
example : lookup1 4 t3 = none := by decide
example : lookup1 0 t3 = none := by decide
example : lookup1 5 t7 = some 6 := by decide
example : lookup1 6 t7 = some 5 := by decide
example : lookup1 7 t7 = some 7 := by decide
example : lookup1 8 t7 = none := by decide

example : update1 9 2 t3 = .Node (.Node .Leaf 9 .Leaf) 1 (.Node .Leaf 3 .Leaf) :=
  by decide
example : update1 9 1 t3 = .Node (.Node .Leaf 2 .Leaf) 9 (.Node .Leaf 3 .Leaf) :=
  by decide
example : update1 9 4 t3 =
    .Node (.Node (.Node .Leaf 9 .Leaf) 2 .Leaf) 1 (.Node .Leaf 3 .Leaf) :=
  by decide

example : ofList [1, 2, 3] = t3 := by decide
example : ofList [1, 2, 3, 4] = t4 := by decide
example : ofList [1, 2, 3, 4, 5] = o5 := by decide
example : ofList ([] : List Nat) = .Leaf := by decide

example : (Array.ofList [1, 2, 3]).toList = [1, 2, 3] :=
  Array.ofList_toList [1, 2, 3]
example : (Array.ofList [1, 2, 3]).lookup 0 = some 1 := by decide
example : (Array.ofList [1, 2, 3]).lookup 1 = some 2 := by decide
example : (Array.ofList [1, 2, 3]).lookup 2 = some 3 := by decide
example : (Array.ofList [1, 2, 3]).lookup 3 = none := by decide
example : ((Array.ofList [1, 2, 3]).update 1 9).toList = [1, 9, 3] :=
  array_update_spec [1, 2, 3] 1 9 (by decide)
example : ((Array.ofList [1, 2, 3]).update 0 9).toList = [9, 2, 3] :=
  array_update_spec [1, 2, 3] 0 9 (by decide)
example : ((Array.ofList [1, 2, 3]).update 2 8).toList = [1, 2, 8] :=
  array_update_spec [1, 2, 3] 2 8 (by decide)

example : Tlookup1 1 t3 = 1 := by decide
example : Tlookup1 2 t3 = 2 := by decide
example : Tlookup1 4 t3 = 3 := by decide
example : Tupdate1 9 2 t3 = 2 := by decide
example : Tupdate1 9 4 t3 = 3 := by decide
example : Tadds ([] : List Nat) 0 .Leaf = 1 := by decide
example : Tadds [1, 2] 0 (.Leaf : Tree Nat) = 6 := by decide

example : nat_of [] = 1 := by decide
example : nat_of [true] = 3 := by decide
example : nat_of [false] = 2 := by decide
example : nat_of [true, false] = 5 := by decide
example : nat_of [false, true] = 6 := by decide

example : lookup_trie t3 [] = some 1 := by decide
example : lookup_trie t3 [false] = some 2 := by decide
example : lookup_trie t3 [true] = some 3 := by decide
example : lookup_trie t3 [false, true] = none := by decide
example : lookup_trie t3 [true, false] = none := by decide
example : lookup_trie (.Leaf : Tree Nat) [true] = none := by decide

example : update_trie [] 9 t3 =
    .Node (.Node .Leaf 2 .Leaf) 9 (.Node .Leaf 3 .Leaf) := by decide
example : update_trie [false] 9 t3 =
    .Node (.Node .Leaf 9 .Leaf) 1 (.Node .Leaf 3 .Leaf) := by decide
example : update_trie [true] 9 t3 =
    .Node (.Node .Leaf 2 .Leaf) 1 (.Node .Leaf 9 .Leaf) := by decide

/-- (11.1): 1-based lookup reads the index-order list. -/
example {α : Type u} {t : Tree α} (h : braun t) (i : ℕ) (hi : 1 ≤ i) :
    lookup1 i t = (list t)[i - 1]? :=
  lookup1_list h i hi

/-- (11.2): the list is the map of 1-based lookups. -/
example {α : Type u} {t : Tree α} (h : braun t) :
    (List.range (size t)).map (fun i => lookup1 (i + 1) t) = (list t).map some :=
  list_eq_map_lookup1 h

/-- In-range lookup is `none` past the end. -/
example {α : Type u} {t : Tree α} (h : braun t) {i : ℕ} (hi : size t < i) :
    lookup1 i t = none :=
  lookup1_eq_none h hi

/-- In-range update preserves the size. -/
example {α : Type u} {t : Tree α} (h : braun t) {n : ℕ} (hn : 1 ≤ n)
    (hn2 : n ≤ size t) (x : α) : size (update1 x n t) = size t :=
  size_update1 h hn hn2 x

/-- In-range update preserves Braunness. -/
example {α : Type u} {t : Tree α} (h : braun t) {n : ℕ} (hn : 1 ≤ n)
    (hn2 : n ≤ size t) (x : α) : braun (update1 x n t) :=
  braun_update1 h hn hn2 x

/-- Lookup after update: the updated position, otherwise unchanged. -/
example {α : Type u} {t : Tree α} (h : braun t) {n : ℕ} (hn : 1 ≤ n)
    (hn2 : n ≤ size t) (x : α) (m : ℕ) :
    lookup1 m (update1 x n t) = if n = m then some x else lookup1 m t :=
  lookup1_update1 h hn hn2 x m

/-- The list after an in-range update is the list with one entry set. -/
example {α : Type u} {t : Tree α} (h : braun t) {n : ℕ} (hn : 1 ≤ n)
    (hn2 : n ≤ size t) (x : α) :
    list (update1 x n t) = (list t).set (n - 1) x :=
  list_update1 h hn hn2 x

/-- Appending: size, Braunness, and list. -/
example {α : Type u} {t : Tree α} (h : braun t) (x : α) :
    size (update1 x (size t + 1) t) = size t + 1 ∧
      braun (update1 x (size t + 1) t) ∧
      list (update1 x (size t + 1) t) = list t ++ [x] :=
  add_hi_spec h x

/-- `ofList` is repeated appending from the empty tree. -/
example {α : Type u} (xs : List α) : ofList xs = adds xs 0 (.Leaf : Tree α) :=
  ofList_eq_adds xs

/-- `ofList` recovers the list. -/
example {α : Type u} (xs : List α) : list (ofList xs) = xs :=
  ofList_list xs

/-- `ofList` produces a Braun tree of the right size. -/
example {α : Type u} (xs : List α) : braun (ofList xs) ∧ size (ofList xs) = xs.length :=
  ⟨ofList_braun xs, ofList_size xs⟩

/-- The array built from a list satisfies the invariant. -/
example {α : Type u} (xs : List α) : (Array.ofList xs).invar :=
  Array.ofList_invar xs

/-- The array built from a list converts back to the list. -/
example {α : Type u} (xs : List α) : (Array.ofList xs).toList = xs :=
  Array.ofList_toList xs

/-- The array built from a list is the book's `array` construction. -/
example {α : Type u} (xs : List α) :
    Array.ofList xs = ⟨adds xs 0 (.Leaf : Tree α), xs.length⟩ :=
  Array.ofList_eq_adds xs

/-- An invariant array's cached size is its list length. -/
example {α : Type u} {a : BraunTree.Array α} (h : a.invar) : a.n = (a.toList).length :=
  Array.invar_len h

/-- (lookup) for an arbitrary invariant array. -/
example {α : Type u} {a : BraunTree.Array α} (h : a.invar) (i : ℕ) :
    a.lookup i = (a.toList)[i]? :=
  array_lookup_spec_invar h i

/-- (update), (update-inv) for an arbitrary invariant array. -/
example {α : Type u} {a : BraunTree.Array α} (h : a.invar) (i : ℕ) (x : α) (hi : i < a.n) :
    ((a.update i x).toList = (a.toList).set i x) ∧ (a.update i x).invar :=
  array_update_spec_invar h i x hi

/-- (lookup) for the array built from a list. -/
example {α : Type u} (xs : List α) (i : ℕ) :
    (Array.ofList xs).lookup i = xs[i]? :=
  array_lookup_spec xs i

/-- (update) for the array built from a list. -/
example {α : Type u} (xs : List α) (i : ℕ) (x : α) (hi : i < xs.length) :
    ((Array.ofList xs).update i x).toList = xs.set i x :=
  array_update_spec xs i x hi

/-- (#10): Braunness is the index-set characterisation. -/
example {α : Type u} {t : Tree α} :
    braun t ↔ braun_indices t = Set.Icc 1 (size t) :=
  braun_iff_indices

/-- Exercise 11.5: trie lookup is 1-based lookup at `nat_of bs`. -/
example {α : Type u} {t : Tree α} {bs : List Bool} (h : braun t)
    (h1 : 1 ≤ nat_of bs) (h2 : nat_of bs ≤ size t) :
    lookup_trie t bs = lookup1 (nat_of bs) t :=
  lookup_trie_spec h h1 h2

/-- Exercise 11.5: trie update is 1-based update at `nat_of bs`. -/
example {α : Type u} {t : Tree α} {bs : List Bool} (x : α) (h : braun t)
    (h1 : 1 ≤ nat_of bs) (h2 : nat_of bs ≤ size t) :
    update_trie bs x t = update1 x (nat_of bs) t :=
  update_trie_spec x h h1 h2

/-- `nat_of` is positive. -/
example (bs : List Bool) : 0 < nat_of bs :=
  nat_of_pos bs

/-- (#33): `lookup1` descends along one branch. -/
example (i : ℕ) (t : Tree Nat) : Tlookup1 i t ≤ height t + 1 :=
  Tlookup1_le i t

/-- (#33): `update1` descends along one branch. -/
example {α : Type u} (x : α) (i : ℕ) (t : Tree α) : Tupdate1 x i t ≤ height t + 1 :=
  Tupdate1_le x i t

/-- (#33): `lookup1` is logarithmic on Braun trees. -/
example {α : Type u} {i : ℕ} {t : Tree α} (h : braun t) :
    Tlookup1 i t ≤ Nat.log2 (size t) + 2 :=
  Tlookup1_le_braun h

/-- (#33): `update1` is logarithmic on Braun trees. -/
example {α : Type u} {x : α} {i : ℕ} {t : Tree α} (h : braun t) :
    Tupdate1 x i t ≤ Nat.log2 (size t) + 2 :=
  Tupdate1_le_braun h

/-- (#34): `list` costs O(|t| · h t). -/
example {α : Type u} (t : Tree α) : Tlist t ≤ (size t + 1) * (height t + 1) :=
  Tlist_le t

/-- (#34): `list` is O(n lg n) on Braun trees. -/
example {α : Type u} {t : Tree α} (h : braun t) :
    Tlist t ≤ (size t + 1) * (Nat.log2 (size t) + 2) :=
  Tlist_le_braun h

/-- (#34): building an array costs O(n lg n) with `n ≤ |t|`. -/
example {α : Type u} (xs : List α) (n : ℕ) (t : Tree α) (h : braun t) (hn : n ≤ size t) :
    Tadds xs n t ≤ (xs.length + 1) * (Nat.log2 (size t + xs.length) + 3) :=
  Tadds_le xs n t h hn

/-- (#34): building an array from a list costs O(n lg n). -/
example {α : Type u} (xs : List α) :
    Tadds xs 0 (.Leaf : Tree α) ≤ (xs.length + 1) * (Nat.log2 xs.length + 3) :=
  Tadds_le_array xs

/-- `log2` is monotone. -/
example {m n : ℕ} (h : m ≤ n) : Nat.log2 m ≤ Nat.log2 n :=
  log2_mono h

/-- `log2` grows by at most one under successor. -/
example (n : ℕ) : Nat.log2 (n + 1) ≤ Nat.log2 n + 1 :=
  log2_succ_le n

/-- Updating at `n + 1` grows the height by at most one. -/
example {α : Type u} (t : Tree α) (h : braun t) {n : ℕ} (hn : n ≤ size t) (x : α) :
    height (update1 x (n + 1) t) ≤ height t + 1 :=
  height_update1_le t h hn x

end Cslib.Algorithms.Lean.BraunTreeArrayTests
