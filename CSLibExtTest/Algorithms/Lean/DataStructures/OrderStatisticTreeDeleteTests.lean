/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.OrderStatisticTree.Delete
public import Mathlib.Data.Nat.Basic

/-!
# Order-statistic tree deletion tests

Executable examples cover empty and absent-key deletion, leaf and two-child/root
merging, repaired subtree-size caches, and rank/select behavior after deletion,
through the public executable and correctness API.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.OrderStatisticTreeDeleteTests

open OrderStatisticTree

/-- The balanced fixture from the parent tests: root `4`, inorder `[1, …, 7]`. -/
public def balanced : OrderStatisticTree.Tree Nat := fromList [7, 5, 3, 1, 6, 2, 4]

public def singleton : OrderStatisticTree.Tree Nat := insert 3 .nil

-- Empty tree and singleton deletion.
example : delete 1 (BinaryTree.nil : OrderStatisticTree.Tree Nat) = .nil := by decide
example : delete 3 singleton = .nil := by decide
example : delete 4 singleton = singleton := by decide
example : cachedSize (delete 3 singleton) = 0 := by decide

-- Absent-key deletion leaves membership, traversal, and size unchanged.
example : inorder (delete 8 balanced) = [1, 2, 3, 4, 5, 6, 7] := by decide
example : inorder (delete 0 balanced) = [1, 2, 3, 4, 5, 6, 7] := by decide
example : cachedSize (delete 8 balanced) = 7 := by decide
example : delete 8 balanced = balanced := by decide
example : contains 5 (delete 8 balanced) = true := by decide

-- Leaf deletion, with the root cache repaired to the new size.
example : inorder (delete 1 balanced) = [2, 3, 4, 5, 6, 7] := by decide
example : cachedSize (delete 1 balanced) = 6 := by decide
example : CacheCorrect (delete 1 balanced) :=
  cacheCorrect_delete cacheCorrect_fromList
example : select (delete 1 balanced) 0 = some 2 := by decide
example : rank 7 (delete 1 balanced) = 5 := by decide

-- Two-child root deletion: the subtrees of `4` are merged.
example : inorder (delete 4 balanced) = [1, 2, 3, 5, 6, 7] := by decide
example : delete 4 balanced =
    node 2 (node 1 .nil .nil)
      (node 3 .nil (node 6 (node 5 .nil .nil) (node 7 .nil .nil))) := by
  decide
example : cachedSize (delete 4 balanced) = 6 := by decide
example : CacheCorrect (delete 4 balanced) :=
  cacheCorrect_delete cacheCorrect_fromList
example : Ordered (delete 4 balanced) := ordered_delete ordered_fromList
example : contains 4 (delete 4 balanced) = false := by decide
example : contains 5 (delete 4 balanced) = true := by decide

-- Rank/select after root deletion navigate by the repaired caches.
example : rank 4 (delete 4 balanced) = 3 := by decide
example : rank 5 (delete 4 balanced) = 3 := by decide
example : rank 7 (delete 4 balanced) = 5 := by decide
example : select (delete 4 balanced) 3 = some 5 := by decide
example : select (delete 4 balanced) 5 = some 7 := by decide
example : select (delete 4 balanced) 6 = none := by decide
example : select (delete 4 balanced) (rank 6 (delete 4 balanced)) = some 6 :=
  select_rank_delete cacheCorrect_fromList ordered_fromList
    ((mem_delete_iff ordered_fromList).mpr
      ⟨mem_fromList.mpr (by decide), by decide⟩)

-- Internal two-child deletion and repeated deletion.
example : inorder (delete 2 balanced) = [1, 3, 4, 5, 6, 7] := by decide
example : inorder (delete 6 balanced) = [1, 2, 3, 4, 5, 7] := by decide
example : inorder (delete 4 (delete 2 (delete 6 balanced))) = [1, 3, 5, 7] := by decide
example : cachedSize (delete 4 (delete 2 (delete 6 balanced))) = 4 := by decide
example : select (delete 4 (delete 2 (delete 6 balanced))) 2 = some 5 := by decide

-- Deletion repairs a stale cache on the search path (executable behavior).
public def badCache : OrderStatisticTree.Tree Nat :=
  .node { key := 2, subtreeSize := 3 }
    (.node { key := 1, subtreeSize := 1 } .nil .nil) .nil

example : cachedSize badCache = 3 := by decide
example : cachedSize (delete 9 badCache) = 2 := by decide
example : delete 9 badCache = node 2 (node 1 .nil .nil) .nil := by decide
example : CacheCorrect (delete 9 badCache) := by
  have h : delete 9 badCache = node 2 (node 1 .nil .nil) .nil := by decide
  rw [h]
  exact cacheCorrect_node (cacheCorrect_node trivial trivial) trivial

-- `merge` of separated trees: traversal, size, caches, and membership.
public def leftPart : OrderStatisticTree.Tree Nat :=
  node 2 (node 1 .nil .nil) (node 3 .nil .nil)
public def rightPart : OrderStatisticTree.Tree Nat :=
  node 6 (node 5 .nil .nil) (node 7 .nil .nil)

example : inorder (merge leftPart rightPart) = [1, 2, 3, 5, 6, 7] := by decide
example : cachedSize (merge leftPart rightPart) = 6 := by decide
example : merge (BinaryTree.nil : OrderStatisticTree.Tree Nat) rightPart = rightPart := by
  decide
example : inorder (merge leftPart (BinaryTree.nil : OrderStatisticTree.Tree Nat)) =
    [1, 2, 3] := by
  decide
example : select (merge leftPart rightPart) 4 = some 6 := by decide

-- Public theorem API on abstract trees.
example {key : Nat} {tree : OrderStatisticTree.Tree Nat} (h : CacheCorrect tree) :
    CacheCorrect (delete key tree) :=
  cacheCorrect_delete h
example {key : Nat} {tree : OrderStatisticTree.Tree Nat} (h : Ordered tree) :
    Ordered (delete key tree) :=
  ordered_delete h
example {key : Nat} {tree : OrderStatisticTree.Tree Nat} (h : Ordered tree) :
    inorder (delete key tree) = (inorder tree).filter (· ≠ key) :=
  inorder_delete h
example {key y : Nat} {tree : OrderStatisticTree.Tree Nat} (h : Ordered tree) :
    y ∈ delete key tree ↔ y ∈ tree ∧ y ≠ key :=
  mem_delete_iff h
example {key : Nat} {tree : OrderStatisticTree.Tree Nat} (h : Ordered tree) :
    key ∉ delete key tree :=
  not_mem_delete h
example {key : Nat} {tree : OrderStatisticTree.Tree Nat} (h : Ordered tree) :
    contains key (delete key tree) = false :=
  contains_delete_self h
example {left right : OrderStatisticTree.Tree Nat}
    (hLeft : CacheCorrect left) (hRight : CacheCorrect right) :
    CacheCorrect (merge left right) :=
  cacheCorrect_merge hLeft hRight
example {left right : OrderStatisticTree.Tree Nat} :
    inorder (merge left right) = inorder left ++ inorder right :=
  inorder_merge
example {x : Nat} {left right : OrderStatisticTree.Tree Nat} :
    x ∈ merge left right ↔ x ∈ left ∨ x ∈ right :=
  mem_merge
example {key query : Nat} {tree : OrderStatisticTree.Tree Nat}
    (hCache : CacheCorrect tree) (hTree : Ordered tree) :
    rank query (delete key tree) =
      BinarySearchTree.rank query (erase (delete key tree)) :=
  rank_delete_eq_bstRank hCache hTree
example {key : Nat} {tree : OrderStatisticTree.Tree Nat}
    (hCache : CacheCorrect tree) (index : Nat) :
    select (delete key tree) index =
      BinarySearchTree.select (erase (delete key tree)) index :=
  select_delete_eq_bstSelect hCache index

#check OrderStatisticTree.merge
#check OrderStatisticTree.delete
#check cacheCorrect_merge
#check cacheCorrect_delete
#check ordered_merge
#check ordered_delete
#check inorder_merge
#check mem_merge
#check inorder_delete
#check mem_delete_iff
#check not_mem_delete
#check contains_delete_self
#check rank_delete_eq_bstRank
#check select_delete_eq_bstSelect
#check select_rank_delete

#print axioms cacheCorrect_merge
#print axioms cacheCorrect_delete
#print axioms ordered_merge
#print axioms ordered_delete
#print axioms inorder_merge
#print axioms mem_merge
#print axioms inorder_delete
#print axioms mem_delete_iff
#print axioms not_mem_delete
#print axioms contains_delete_self
#print axioms rank_delete_eq_bstRank
#print axioms select_delete_eq_bstSelect
#print axioms select_rank_delete

end Cslib.Algorithms.Lean.OrderStatisticTreeDeleteTests
