/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.OrderStatisticTree
public import Mathlib.Data.Nat.Basic

/-! Importing tests for the cached order-statistic tree. -/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.OrderStatisticTreeTests

open OrderStatisticTree

private def singleton : OrderStatisticTree.Tree Nat := insert 3 .nil

/-- A balanced fixture shared by the executable tests in this module. -/
public def balanced : OrderStatisticTree.Tree Nat := fromList [7, 5, 3, 1, 6, 2, 4]

private def ascending : OrderStatisticTree.Tree Nat := fromList [1, 2, 3, 4]

private def descending : OrderStatisticTree.Tree Nat := fromList [4, 3, 2, 1]

private def expectedBalanced : OrderStatisticTree.Tree Nat :=
  node 4
    (node 2 (node 1 .nil .nil) (node 3 .nil .nil))
    (node 6 (node 5 .nil .nil) (node 7 .nil .nil))

example : CacheCorrect (BinaryTree.nil : OrderStatisticTree.Tree Nat) := trivial
example : contains 1 (BinaryTree.nil : OrderStatisticTree.Tree Nat) = false := by decide
example : rank 1 (BinaryTree.nil : OrderStatisticTree.Tree Nat) = 0 := by decide
example : select (BinaryTree.nil : OrderStatisticTree.Tree Nat) 0 = none := by decide

example : cachedSize singleton = 1 := by decide
example : contains 3 singleton = true := by decide
example : contains 2 singleton = false := by decide
example : select singleton 0 = some 3 := by decide
example : select singleton 1 = none := by decide

example : CacheCorrect balanced := cacheCorrect_fromList

/-- Insertion membership is available downstream through the public
`erase_insert` refinement and the prerequisite `BinarySearchTree.mem_insert`. -/
example {x y : Nat} {tree : OrderStatisticTree.Tree Nat} :
    y ∈ insert x tree ↔ y = x ∨ y ∈ tree := by
  have h : (y ∈ insert x tree) ↔
      (y ∈ BinarySearchTree.insert x (erase tree)) := by
    rw [← erase_insert]
    exact Iff.rfl
  exact h.trans BinarySearchTree.mem_insert


/-- The empty tree is trivially cache-correct. -/
private theorem cacheCorrect_nil {α : Type} :
    CacheCorrect (.nil : OrderStatisticTree.Tree α) :=
  trivial

/-- Downstream users can establish `CacheCorrect` for `node`-assembled trees
through the public API. -/
example : CacheCorrect (node 2 (node 1 .nil .nil) (node 3 .nil .nil)) :=
  cacheCorrect_node (cacheCorrect_node cacheCorrect_nil cacheCorrect_nil)
    (cacheCorrect_node cacheCorrect_nil cacheCorrect_nil)

/-- A correctly cached tree over a key type with no linear order: the keys are
functions, and `select` refinement must not require ordering. -/
private def unorderedTree : OrderStatisticTree.Tree (Nat → Nat) :=
  node id (node (· + 1) .nil .nil) .nil

example : CacheCorrect unorderedTree :=
  cacheCorrect_node (cacheCorrect_node cacheCorrect_nil cacheCorrect_nil)
    cacheCorrect_nil

/-- Select refinement for the unordered tree, proved without any `LinearOrder`
instance or `Ordered` hypothesis. -/
example : select unorderedTree 1 =
    BinarySearchTree.select (erase unorderedTree) 1 :=
  select_eq_bstSelect (cacheCorrect_node
    (cacheCorrect_node cacheCorrect_nil cacheCorrect_nil) cacheCorrect_nil) 1

example : Ordered balanced := ordered_fromList
example : balanced = expectedBalanced := by decide
example : inorder balanced = [1, 2, 3, 4, 5, 6, 7] := by decide
example : inorder ascending = [1, 2, 3, 4] := by decide
example : inorder descending = [1, 2, 3, 4] := by decide

example : insert 4 balanced = balanced := by decide
example : cachedSize (insert 4 balanced) = cachedSize balanced := by decide
example : CacheCorrect (insert 8 balanced) := cacheCorrect_insert cacheCorrect_fromList
example : Ordered (insert 8 balanced) := ordered_insert ordered_fromList

example : rank 1 balanced = 0 := by decide
example : rank 7 balanced = 6 := by decide
example : rank 8 balanced = 7 := by decide
example : select balanced 0 = some 1 := by decide
example : select balanced 6 = some 7 := by decide
example : select balanced 7 = none := by decide

example : select balanced (rank 5 balanced) = some 5 :=
  select_rank cacheCorrect_fromList ordered_fromList (mem_fromList.mpr (by simp))

example : rank 6 balanced = 5 :=
  rank_select cacheCorrect_fromList ordered_fromList (by decide)

private def badCache : OrderStatisticTree.Tree Nat :=
  .node { key := 2, subtreeSize := 3 }
    (.node { key := 1, subtreeSize := 1 } .nil .nil) .nil

example : ¬CacheCorrect badCache := by simp [badCache, CacheCorrect]

#check OrderStatisticTree.Tree
#check CacheCorrect
#check Ordered
#check erase
#check contains
#check OrderStatisticTree.insert
#check rank
#check select
#check cachedSize_eq_numNodes
#check cacheCorrect_insert
#check ordered_insert
#check contains_eq_true_iff
#check rank_eq_bstRank
#check select_eq_bstSelect
#check select_rank
#check rank_select

#print axioms cachedSize_eq_numNodes
#print axioms cacheCorrect_insert
#print axioms ordered_insert
#print axioms cacheCorrect_fromList
#print axioms ordered_fromList
#print axioms mem_fromList
#print axioms contains_eq_true_iff
#print axioms rank_eq_bstRank
#print axioms select_eq_bstSelect
#print axioms select_rank
#print axioms rank_select

end Cslib.Algorithms.Lean.OrderStatisticTreeTests
