/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Keep the API under test: anonymous examples are not dependency roots for shake.
import CSLibExt.Algorithms.Lean.DataStructures.AvlTree.Complexity -- shake: keep

/-!
# AVL counted-operation consumers

Exact small computations protect the tick model as well as return-value erasure.
The generic consumers compose with the current `Valid` and inorder API. False-cache
and unbalanced examples keep both hypotheses of the logarithmic bound load-bearing.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.AvlTree

namespace Cslib.Algorithms.Lean.AvlTree.ComplexityTests

private def leaf (x : Nat) : Tree Nat := mkNode .empty x .empty
private def three : Tree Nat := mkNode (leaf 1) 2 (leaf 3)
private def seven : Tree Nat := mkNode three 4 (mkNode (leaf 5) 6 (leaf 7))

/-! ## Empty and singleton boundaries -/

example : size (.empty : Tree Nat) = 0 := by simp
example : size three = 3 := by decide
example : height three = (toBinaryTree three).height :=
  height_eq_of_cacheCorrect (by simp [three, leaf, CacheCorrect, mkNode])

example : ((containsT 1 (.empty : Tree Nat)).ret, (containsT 1 .empty).time) =
    (false, 0) := by decide
example : ((insertT 1 (.empty : Tree Nat)).ret, (insertT 1 .empty).time) =
    (leaf 1, 1) := by decide
example : ((deleteT 1 (.empty : Tree Nat)).ret, (deleteT 1 .empty).time) =
    (.empty, 0) := by decide
example : ((minDT 7 (.empty : Tree Nat)).ret, (minDT 7 .empty).time) = (7, 0) := by
  decide
example : ((eraseMinT (.empty : Tree Nat)).ret, (eraseMinT (.empty : Tree Nat)).time) =
    (.empty, 0) := by decide
example : ((mkNodeT (.empty : Tree Nat) 1 .empty).ret,
    (mkNodeT (.empty : Tree Nat) 1 .empty).time) = (leaf 1, 1) := by decide

example : ((containsT 1 (leaf 1)).ret, (containsT 1 (leaf 1)).time) = (true, 3) := by
  decide
example : ((insertT 1 (leaf 1)).ret, (insertT 1 (leaf 1)).time) = (leaf 1, 3) := by
  decide
example : ((deleteT 1 (leaf 1)).ret, (deleteT 1 (leaf 1)).time) = (.empty, 3) := by
  decide
example : ((minDT 7 (leaf 1)).ret, (minDT 7 (leaf 1)).time) = (1, 1) := by decide
example : ((eraseMinT (leaf 1)).ret, (eraseMinT (leaf 1)).time) = (.empty, 1) := by
  decide

/-! ## Both comparison directions, duplicates, and absent deletion -/

example : ((containsT 1 three).ret, (containsT 1 three).time) = (true, 5) := by decide
example : ((containsT 3 three).ret, (containsT 3 three).time) = (true, 6) := by decide
example : ((containsT 0 three).ret, (containsT 0 three).time) = (false, 4) := by decide
example : ((containsT 4 three).ret, (containsT 4 three).time) = (false, 6) := by decide
example : ((insertT 2 three).ret, (insertT 2 three).time) = (three, 3) := by decide
example : ((deleteT 0 three).ret, (deleteT 0 three).time) = (three, 6) := by decide
example : ((deleteT 4 three).ret, (deleteT 4 three).time) = (three, 8) := by decide

/-! ## Local rebalancing: one rebuild, two single rotations, two double rotations -/

example : ((balanceT (leaf 1) 2 (leaf 3)).ret,
    (balanceT (leaf 1) 2 (leaf 3)).time) = (three, 1) := by decide
example : ((balanceT (mkNode (leaf 1) 2 .empty) 3 .empty).ret,
    (balanceT (mkNode (leaf 1) 2 .empty) 3 .empty).time) = (three, 3) := by decide
example : ((balanceT .empty 1 (mkNode .empty 2 (leaf 3))).ret,
    (balanceT .empty 1 (mkNode .empty 2 (leaf 3))).time) = (three, 3) := by decide
example : ((balanceT (mkNode .empty 1 (leaf 2)) 3 .empty).ret,
    (balanceT (mkNode .empty 1 (leaf 2)) 3 .empty).time) = (three, 5) := by decide
example : ((balanceT .empty 1 (mkNode (leaf 2) 3 .empty)).ret,
    (balanceT .empty 1 (mkNode (leaf 2) 3 .empty)).time) = (three, 5) := by decide

-- Full insertions charge search, the new leaf, and all rotation rebuilds.
example : ((insertT 1 (mkNode (leaf 2) 3 .empty)).ret,
    (insertT 1 (mkNode (leaf 2) 3 .empty)).time) = (three, 9) := by decide
example : ((insertT 3 (mkNode .empty 1 (leaf 2))).ret,
    (insertT 3 (mkNode .empty 1 (leaf 2))).time) = (three, 11) := by decide
example : ((insertT 2 (mkNode (leaf 1) 3 .empty)).ret,
    (insertT 2 (mkNode (leaf 1) 3 .empty)).time) = (three, 12) := by decide
example : ((insertT 2 (mkNode .empty 1 (leaf 3))).ret,
    (insertT 2 (mkNode .empty 1 (leaf 3))).time) = (three, 12) := by decide

/-! ## One-child splicing and both successor traversals -/

example : ((deleteT 2 (mkNode (leaf 1) 2 .empty)).ret,
    (deleteT 2 (mkNode (leaf 1) 2 .empty)).time) = (leaf 1, 3) := by decide
example : ((deleteT 1 (mkNode .empty 1 (leaf 2))).ret,
    (deleteT 1 (mkNode .empty 1 (leaf 2))).time) = (leaf 2, 3) := by decide
example : ((deleteT 2 three).ret, (deleteT 2 three).time) =
    (mkNode (leaf 1) 3 .empty, 6) := by decide
example : (minDT 4 (mkNode (leaf 5) 6 (leaf 7))).time = 2 := by decide
example : (eraseMinT (mkNode (leaf 5) 6 (leaf 7))).time = 3 := by decide
-- Root visit + two comparisons + two min visits + three erase-min ticks + rebuild.
example : (deleteT 4 seven).time = 3 + 2 + 3 + 1 := by decide
example : (deleteT 4 seven).ret = delete 4 seven := by decide
example : inorder (deleteT 4 seven).ret = [1, 2, 3, 5, 6, 7] := by decide

/-! ## Public API, invariant closure and log bounds on current operations -/

universe u
variable {α : Type u}

example (l r : Tree α) (x : α) : (balanceT l x r).ret = balance l x r := by simp
example [LinearOrder α] (x : α) (t : Tree α) : (containsT x t).ret = contains x t := by
  simp
example [LinearOrder α] (x : α) (t : Tree α) : (insertT x t).ret = insert x t := by simp
example [LinearOrder α] (x : α) (t : Tree α) : (eraseT x t).ret = erase x t := by simp
example [LinearOrder α] (x : α) (t : Tree α) : (deleteT x t).ret = delete x t := by simp
example (d : α) (t : Tree α) : (minDT d t).ret = minD d t := by simp
example (t : Tree α) : (eraseMinT t).ret = eraseMin t := by simp

example [LinearOrder α] (x : α) {t : Tree α} (h : Valid t) :
    Valid (insertT x t).ret := by
  simpa only [ret_insertT] using (valid_insert (x := x) h)
example [LinearOrder α] (x : α) {t : Tree α} (h : Valid t) :
    Valid (deleteT x t).ret := by
  simpa only [ret_deleteT] using (valid_delete (x := x) h)
example [LinearOrder α] (x : α) {t : Tree α} (h : Valid t) :
    (containsT x t).ret = true ↔ x ∈ t := by
  simpa only [ret_containsT] using (contains_eq_true_iff (x := x) h.1)
example [LinearOrder α] (x y : α) (t : Tree α) :
    y ∈ (insertT x t).ret ↔ y = x ∨ y ∈ t := by
  simpa only [ret_insertT] using (mem_insert (x := x) (y := y) (tree := t))
example [LinearOrder α] (x : α) {t : Tree α} (h : Valid t) :
    inorder (deleteT x t).ret = (inorder t).erase x := by
  simpa only [ret_deleteT] using (inorder_delete (x := x) h.1)

example [LT α] {t : Tree α} (h : Valid t) :
    height t ≤ 2 * Nat.log2 (size t + 1) + 1 := height_le_log2 h.2.1 h.2.2
example [LinearOrder α] (x : α) {t : Tree α} (h : Valid t) :
    (containsT x t).time ≤ 6 * (Nat.log2 (size t + 1) + 1) :=
  time_containsT_le_log2 x h.2.1 h.2.2
example [LinearOrder α] (x : α) {t : Tree α} (h : Valid t) :
    (insertT x t).time ≤ 16 * (Nat.log2 (size t + 1) + 1) :=
  time_insertT_le_log2 x h.2.1 h.2.2
example [LinearOrder α] (x : α) {t : Tree α} (h : Valid t) :
    (deleteT x t).time ≤ 16 * (Nat.log2 (size t + 1) + 1) :=
  time_deleteT_le_log2 x h.2.1 h.2.2
example [LinearOrder α] (x y : α) {t : Tree α} (h : Valid t) :
    (containsT y (deleteT x t).ret).time ≤
      6 * (Nat.log2 (size (deleteT x t).ret + 1) + 1) := by
  have hv : Valid (deleteT x t).ret := by
    simpa only [ret_deleteT] using (valid_delete (x := x) h)
  exact time_containsT_le_log2 y hv.2.1 hv.2.2

example : height (.empty : Tree Nat) ≤ 2 * Nat.log2 (size (.empty : Tree Nat) + 1) + 1 :=
  height_le_log2 trivial trivial
example : Nat.fib (height seven + 2) ≤ size seven + 1 :=
  fib_le_size_succ (by simp [seven, three, leaf, CacheCorrect, mkNode])
    (by simp [seven, three, leaf, Balanced, mkNode])

/-! ## Negative models: both height hypotheses matter -/

-- Balanced constrains children, not the root's stored height.
private def falseCache : Tree Nat := .node 100 .empty 1 .empty
example : Balanced falseCache := by simp [falseCache, Balanced]
example : Ordered falseCache := by
  simp [falseCache, Ordered, toBinaryTree, BinarySearchTree.Ordered, BinarySearchTree.All]
example : ¬ CacheCorrect falseCache := by simp [falseCache, CacheCorrect]
example : ¬ Valid falseCache := by simp [falseCache, Valid, CacheCorrect]
example : ¬ (height falseCache ≤ 2 * Nat.log2 (size falseCache + 1) + 1) := by decide
-- Erasure still promises complete output equality on malformed input.
example : (insertT 0 falseCache).ret = insert 0 falseCache := by decide
example : (deleteT 1 falseCache).ret = delete 1 falseCache := by decide

private def zeroCacheSpine : Nat → Tree Nat
  | 0 => .empty
  | n + 1 => .node 0 .empty 0 (zeroCacheSpine n)

example : Balanced (zeroCacheSpine 8) := by simp [zeroCacheSpine, Balanced]
example : ¬ CacheCorrect (zeroCacheSpine 8) := by simp [zeroCacheSpine, CacheCorrect]
example : (toBinaryTree (zeroCacheSpine 8)).height >
    2 * Nat.log2 (size (zeroCacheSpine 8) + 1) + 1 := by decide
example : (containsT 1 (zeroCacheSpine 8)).time > 3 * height (zeroCacheSpine 8) := by decide

private def correctCacheSpine : Nat → Tree Nat
  | 0 => .empty
  | n + 1 => mkNode .empty n (correctCacheSpine n)

example : CacheCorrect (correctCacheSpine 8) := by
  simp [correctCacheSpine, CacheCorrect, mkNode]
example : ¬ Balanced (correctCacheSpine 8) := by simp [correctCacheSpine, Balanced, mkNode]
example : height (correctCacheSpine 8) >
    2 * Nat.log2 (size (correctCacheSpine 8) + 1) + 1 := by decide

end Cslib.Algorithms.Lean.AvlTree.ComplexityTests
