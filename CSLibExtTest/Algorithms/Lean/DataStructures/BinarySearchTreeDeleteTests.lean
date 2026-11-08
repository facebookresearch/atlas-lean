/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree.Delete
public import Mathlib.Data.Nat.Basic

/-!
# Binary search tree deletion tests

Executable examples cover empty and absent-key deletion, leaf and one-child deletion,
two-child root splicing with `join`, ordering and inorder preservation, and the public
theorem and axiom surface of the deletion module.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace BinarySearchTreeDeleteTests

open BinarySearchTree

public def singleton : BinaryTree Nat := .node 3 .nil .nil
public def populated : BinaryTree Nat := fromList [3, 1, 4, 2]

-- Empty tree and absent keys.
example : delete 5 (BinaryTree.nil : BinaryTree Nat) = .nil := by decide
example : inorder (delete 5 (BinaryTree.nil : BinaryTree Nat)) = [] := by decide
example : inorder (delete 5 populated) = [1, 2, 3, 4] := by decide
example : (delete 5 populated).numNodes = 4 := by decide
example : delete 0 populated = populated := by decide

-- Singleton: deleting the only key empties the tree; deleting another key keeps it.
example : delete 3 singleton = .nil := by decide
example : delete 4 singleton = singleton := by decide

-- Leaf deletion (`1` and `3` are leaves of `populated`).
example : inorder (delete 1 populated) = [2, 3, 4] := by decide
example : inorder (delete 3 populated) = [1, 2, 4] := by decide

-- One-child deletion (`4` has only the left child `3` in `populated`).
example : inorder (delete 4 populated) = [1, 2, 3] := by decide

-- Two-child root deletion (`2` is the root of `populated`, with both children).
example : inorder (delete 2 populated) = [1, 3, 4] := by decide
example : (delete 2 populated).numNodes = 3 := by decide

/-- An explicit tree for structural splicing checks. -/
public def balanced : BinaryTree Nat :=
  .node 3 (.node 1 .nil (.node 2 .nil .nil)) (.node 4 .nil .nil)

-- One-child splicing: deleting `1` replaces it by its right subtree.
example : delete 1 balanced = .node 3 (.node 2 .nil .nil) (.node 4 .nil .nil) := by
  decide

-- Two-child root splicing: the subtrees of `3` are joined end to end.
example : delete 3 balanced =
    .node 1 .nil (.node 2 .nil (.node 4 .nil .nil)) := by
  decide
example : inorder (delete 3 balanced) = [1, 2, 4] := by decide

-- `join` on concrete trees, including the empty splices.
example : join (BinaryTree.nil : BinaryTree Nat) singleton = singleton := by decide
example : inorder (join singleton (BinaryTree.nil : BinaryTree Nat)) = [3] := by decide
example : inorder (join (.node 1 .nil (.node 2 .nil .nil)) (.node 4 .nil .nil)) =
    [1, 2, 4] := by
  decide

-- Repeated deletion drains the tree in inorder.
example : inorder (delete 1 (delete 4 (delete 3 populated))) = [2] := by decide
example : delete 2 (delete 1 (delete 4 (delete 3 populated))) = .nil := by decide

-- Search after deletion sees exactly the remaining keys.
example : contains 3 (delete 3 populated) = false := by decide
example : contains 2 (delete 3 populated) = true := by decide
example : contains 4 (delete 3 populated) = true := by decide

-- Ordering and inorder preservation through the public theorems.
example : Ordered (delete 3 populated) := ordered_delete ordered_fromList
example : Ordered (delete 5 populated) := ordered_delete ordered_fromList
example : inorder (delete 3 populated) = (inorder populated).erase 3 :=
  inorder_delete ordered_fromList
example : inorder (delete 5 populated) = (inorder populated).erase 5 :=
  inorder_delete ordered_fromList
example : 3 ∉ delete 3 populated := not_mem_delete_self ordered_fromList
example : 2 ∈ delete 3 populated :=
  mem_delete_of_mem (mem_fromList.mpr (by decide)) (by decide)
example (y : Nat) : y ∈ delete 3 populated ↔ y ∈ populated ∧ y ≠ 3 :=
  mem_delete ordered_fromList

-- Abstract `join`/`delete` theorem API.
example {x : Nat} {left right : BinaryTree Nat} :
    x ∈ join left right ↔ x ∈ left ∨ x ∈ right :=
  mem_join
example {left right : BinaryTree Nat} :
    inorder (join left right) = inorder left ++ inorder right :=
  inorder_join
example {left right : BinaryTree Nat} (hLeft : Ordered left) (hRight : Ordered right)
    (hSeparated : ∀ a ∈ left, ∀ b ∈ right, a < b) : Ordered (join left right) :=
  ordered_join hLeft hRight hSeparated
example {x : Nat} {tree : BinaryTree Nat} (hTree : Ordered tree) :
    Ordered (delete x tree) :=
  ordered_delete hTree
example {x : Nat} {tree : BinaryTree Nat} (hTree : Ordered tree) :
    inorder (delete x tree) = (inorder tree).erase x :=
  inorder_delete hTree

#check BinarySearchTree.join
#check BinarySearchTree.delete
#check mem_join
#check inorder_join
#check ordered_join
#check mem_delete_of_mem
#check not_mem_delete_self
#check mem_delete
#check ordered_delete
#check inorder_delete

#print axioms mem_join
#print axioms inorder_join
#print axioms ordered_join
#print axioms mem_delete_of_mem
#print axioms not_mem_delete_self
#print axioms mem_delete
#print axioms ordered_delete
#print axioms inorder_delete

end BinarySearchTreeDeleteTests
end Cslib.Algorithms.Lean
