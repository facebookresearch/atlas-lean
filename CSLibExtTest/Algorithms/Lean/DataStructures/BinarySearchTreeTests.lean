/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree
public import Mathlib.Data.Nat.Basic

/-!
# Binary search tree tests

Executable examples cover the canonical carrier, ordering invariant, structural
membership, comparison search, insertion, traversal, node count, rank, and select.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace BinarySearchTreeTests

open BinarySearchTree

private def singleton : BinaryTree Nat := .node 3 .nil .nil
private def populated : BinaryTree Nat := fromList [3, 1, 4, 2]
private def invalid : BinaryTree Nat := .node 3 (.node 5 .nil .nil) .nil

example : ¬5 ∈ (BinaryTree.nil : BinaryTree Nat) := by
  intro h
  exact h
example : contains 5 (BinaryTree.nil : BinaryTree Nat) = false := by decide
example : (BinaryTree.nil : BinaryTree Nat).numNodes = 0 := by decide
example : inorder (BinaryTree.nil : BinaryTree Nat) = [] := by simp

example : 3 ∈ singleton := Or.inr (Or.inl rfl)
example : contains 3 singleton = true := by decide
example : Ordered singleton := by simp [singleton, Ordered, All]
example : inorder singleton = [3] := by decide
example (left right : BinaryTree Nat) :
    inorder (.node 3 left right) = inorder left ++ 3 :: inorder right := by
  simp
example : singleton.numNodes = 1 := by decide

example : insert 3 singleton = singleton := by decide
example : (insert 3 singleton).numNodes = singleton.numNodes := by decide
example : (insert 3 populated).numNodes = populated.numNodes :=
  numNodes_insert_of_mem ordered_fromList (mem_fromList.mpr (by simp))
example : (insert 5 populated).numNodes = populated.numNodes + 1 :=
  numNodes_insert_of_not_mem (by
    intro h
    have : 5 ∈ [3, 1, 4, 2] := mem_fromList.mp h
    simp at this)

example : inorder (fromList [1, 2, 3]) = [1, 2, 3] := by decide
example : inorder (fromList [3, 2, 1]) = [1, 2, 3] := by decide
example : Ordered populated := ordered_fromList
example : inorder populated = [1, 2, 3, 4] := by decide
example : populated.numNodes = 4 := by decide

example : contains 2 populated = true := by decide
example : contains 5 populated = false := by decide

example : rank 3 (BinaryTree.nil : BinaryTree Nat) = 0 := by decide
example : rank 1 populated = 0 := by decide
example : rank 3 populated = 2 := by decide
example : rank 5 populated = 4 := by decide

example : select (BinaryTree.nil : BinaryTree Nat) 0 = none := by decide
example : select populated 0 = some 1 := by decide
example : select populated 2 = some 3 := by decide
example : select populated 4 = none := by decide

example : select populated (rank 4 populated) = some 4 :=
  select_rank ordered_fromList (mem_fromList.mpr (by simp))
example : rank 2 populated = 1 := rank_select ordered_fromList (by decide)

example : 5 ∈ invalid := Or.inl (Or.inr (Or.inl rfl))
example : contains 5 invalid = false := by decide
example : ¬Ordered invalid := by simp [invalid, Ordered, All]

#check BinaryTree
#check BinaryTree.numNodes
#check Ordered
#check BinarySearchTree.insert
#check rank
#check select
#check select_rank
#check rank_select

#print axioms all_iff_forall_mem
#print axioms mem_inorder
#print axioms mem_insert
#print axioms ordered_insert
#print axioms contains_eq_true_iff
#print axioms ordered_inorder
#print axioms inorder_nodup
#print axioms ordered_fromList
#print axioms mem_fromList
#print axioms numNodes_eq_length_inorder
#print axioms numNodes_insert_of_mem
#print axioms numNodes_insert_of_not_mem
#print axioms rank_eq_count_inorder
#print axioms select_eq_getElem?_inorder
#print axioms select_rank
#print axioms rank_select

end BinarySearchTreeTests
end Cslib.Algorithms.Lean
