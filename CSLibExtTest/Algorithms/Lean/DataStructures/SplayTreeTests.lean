/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SplayTree
public import Mathlib.Data.Nat.Basic

/-!
# Tests for the splay-tree API

Client examples exercise every splay rotation case, including the
unsuccessful left-right and right-left (zig-zag) searches where the
last visited node must be rotated to the root, plus split, insertion,
access, and membership through the public API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SplayTreeTests

open BinarySearchTree

private def leaf (x : Nat) : BinaryTree Nat := .node x .nil .nil

/-- Balanced ordered tree over `[1, 2, 3, 4, 5, 6, 7]`. -/
private def balanced : BinaryTree Nat := fromList [4, 2, 6, 1, 3, 5, 7]

private theorem ordered_balanced : Ordered balanced := ordered_fromList

example : SplayTree.splay 3 (BinaryTree.nil : BinaryTree Nat) =
    (BinaryTree.nil : BinaryTree Nat) := by
  decide

example : SplayTree.root? (SplayTree.splay 4 balanced) = some 4 := by
  decide

example : SplayTree.root? (SplayTree.splay 1 balanced) = some 1 := by
  decide

example : SplayTree.root? (SplayTree.splay 7 balanced) = some 7 := by
  decide

example : SplayTree.root? (SplayTree.splay 3 balanced) = some 3 := by
  decide

example : SplayTree.root? (SplayTree.splay 5 balanced) = some 5 := by
  decide

example : inorder (SplayTree.splay 3 balanced) = [1, 2, 3, 4, 5, 6, 7] := by
  decide

/-- Regression: an unsuccessful left-right search splays the last
visited node (`5`) to the root instead of leaving `10` there. -/
example :
    SplayTree.splay 7 (.node 10 (.node 5 .nil .nil) .nil : BinaryTree Nat) =
      .node 5 .nil (.node 10 .nil .nil) := by
  decide

example :
    SplayTree.root? (SplayTree.splay 7
      (.node 10 (.node 5 .nil .nil) .nil : BinaryTree Nat)) = some 5 := by
  decide

/-- Regression: the mirrored unsuccessful right-left search splays the
last visited node (`5`) to the root. -/
example :
    SplayTree.splay 3 (.node 0 .nil (.node 5 .nil .nil) : BinaryTree Nat) =
      .node 5 (.node 0 .nil .nil) .nil := by
  decide

example :
    SplayTree.root? (SplayTree.splay 3
      (.node 0 .nil (.node 5 .nil .nil) : BinaryTree Nat)) = some 5 := by
  decide

/-- Unsuccessful left-right search with a nonempty far subtree: the
final zig keeps `3` below `5` and `12` below `10`. -/
example :
    SplayTree.splay 7
        (.node 10 (.node 5 (leaf 3) .nil) (leaf 12) : BinaryTree Nat) =
      .node 5 (leaf 3) (.node 10 .nil (leaf 12)) := by
  decide

/-- Unsuccessful right-left search with a nonempty far subtree. -/
example :
    SplayTree.splay 8
        (.node 5 (leaf 2) (.node 10 .nil (leaf 12)) : BinaryTree Nat) =
      .node 10 (.node 5 (leaf 2) .nil) (leaf 12) := by
  decide

example :
    inorder (SplayTree.splay 7
      (.node 10 (.node 5 .nil .nil) .nil : BinaryTree Nat)) = [5, 10] := by
  decide

example :
    inorder (SplayTree.splay 3
      (.node 0 .nil (.node 5 .nil .nil) : BinaryTree Nat)) = [0, 5] := by
  decide

example (x : Nat) (t : BinaryTree Nat) :
    inorder (SplayTree.splay x t) = inorder t :=
  SplayTree.inorder_splay t

example (x y : Nat) (t : BinaryTree Nat) :
    y ∈ SplayTree.splay x t ↔ y ∈ t :=
  SplayTree.mem_splay

example (x : Nat) (t : BinaryTree Nat) :
    (SplayTree.splay x t).numNodes = t.numNodes :=
  SplayTree.numNodes_splay

example : Ordered balanced := ordered_balanced

example (x : Nat) : Ordered (SplayTree.splay x balanced) :=
  SplayTree.ordered_splay ordered_balanced

example : SplayTree.root? (SplayTree.splay 6 balanced) = some 6 :=
  SplayTree.root?_splay_of_mem ordered_balanced
    (mem_fromList.mpr (by simp))

example : SplayTree.contains 6 balanced = true := by
  decide

example : SplayTree.contains 8 balanced = false := by
  decide

example : (SplayTree.access 6 balanced).1 = true := by
  decide

example : (SplayTree.access 6 balanced).2 = SplayTree.splay 6 balanced :=
  SplayTree.access_snd

example : SplayTree.root? (SplayTree.insert 0 balanced) = some 0 :=
  SplayTree.root?_insert

example : inorder (SplayTree.insert 0 balanced) = [0, 1, 2, 3, 4, 5, 6, 7] := by
  decide

example : inorder (SplayTree.insert 4 balanced) = [1, 2, 3, 4, 5, 6, 7] := by
  decide

example (x y : Nat) (t : BinaryTree Nat) :
    y ∈ SplayTree.insert x t ↔ y = x ∨ y ∈ t :=
  SplayTree.mem_insert

example : Ordered (SplayTree.insert 0 balanced) :=
  SplayTree.ordered_insert ordered_balanced

example : inorder (SplayTree.split 4 balanced).1 = [1, 2, 3] := by
  decide

example : inorder (SplayTree.split 4 balanced).2 = [5, 6, 7] := by
  decide

example (x : Nat) :
    All (· < x) (SplayTree.split x balanced).1 ∧
      All (x < ·) (SplayTree.split x balanced).2 :=
  SplayTree.all_split ordered_balanced

example (x : Nat) :
    Ordered (SplayTree.split x balanced).1 ∧
      Ordered (SplayTree.split x balanced).2 :=
  SplayTree.ordered_split ordered_balanced

#check SplayTree.splay
#check SplayTree.split
#check SplayTree.insert
#check SplayTree.access
#check SplayTree.contains
#check SplayTree.root?
#check SplayTree.inorder_splay
#check SplayTree.mem_splay
#check SplayTree.numNodes_splay
#check SplayTree.ordered_splay
#check SplayTree.root_splay_of_mem
#check SplayTree.root?_splay_of_mem
#check SplayTree.mem_insert
#check SplayTree.ordered_insert
#check SplayTree.contains_eq_true_iff

#print axioms SplayTree.inorder_splay
#print axioms SplayTree.mem_splay
#print axioms SplayTree.numNodes_splay
#print axioms SplayTree.ordered_splay
#print axioms SplayTree.root_splay_of_mem
#print axioms SplayTree.root?_splay_of_mem
#print axioms SplayTree.mem_of_mem_split
#print axioms SplayTree.mem_split_of_mem
#print axioms SplayTree.all_split
#print axioms SplayTree.ordered_split
#print axioms SplayTree.mem_insert
#print axioms SplayTree.ordered_insert
#print axioms SplayTree.root?_insert
#print axioms SplayTree.contains_eq_true_iff

end Cslib.Algorithms.Lean.SplayTreeTests
