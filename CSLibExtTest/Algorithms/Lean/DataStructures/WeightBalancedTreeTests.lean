/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.WeightBalancedTree

/-!
# Tests for the weight-balanced tree API

These client examples exercise all four rotation branches of `balance`,
duplicate insertion, ordering and balance of built trees, and search over
the shared `BinaryTree` carrier.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.WeightBalancedTreeTests

open WeightBalancedTree

public def insList (xs : List Nat) : BinaryTree Nat :=
  xs.foldl (fun t x => insert x t) .nil

example : insList [] = .nil := rfl

example : insList [2, 2] = .node 2 .nil .nil := by decide

example : insList [1, 2, 3] =
    .node 1 .nil (.node 2 .nil (.node 3 .nil .nil)) := by decide

example : insList [3, 2, 1] =
    .node 3 (.node 2 (.node 1 .nil .nil) .nil) .nil := by decide

/-- Left single rotation: the heavy left child is promoted. -/
example : balance
    (.node 4 (.node 3 (.node 2 (.node 1 .nil .nil) .nil) .nil) .nil) 9 .nil =
    .node 4 (.node 3 (.node 2 (.node 1 .nil .nil) .nil) .nil)
      (.node 9 .nil .nil) := by decide

/-- Left double rotation: the heavy left-right grandchild is promoted. -/
example : balance
    (.node 5 (.node 1 .nil .nil)
      (.node 40 (.node 30 .nil .nil) (.node 50 .nil .nil))) 9 .nil =
    .node 40 (.node 5 (.node 1 .nil .nil) (.node 30 .nil .nil))
      (.node 9 (.node 50 .nil .nil) .nil) := by decide

/-- Right single rotation: the heavy right child is promoted. -/
example : balance .nil 0
    (.node 5 .nil (.node 6 .nil (.node 7 .nil (.node 8 .nil .nil)))) =
    .node 5 (.node 0 .nil .nil)
      (.node 6 .nil (.node 7 .nil (.node 8 .nil .nil))) := by decide

/-- Right double rotation: the heavy right-left grandchild is promoted. -/
example : balance .nil 0
    (.node 5 (.node 40 (.node 30 .nil .nil) (.node 50 .nil .nil))
      (.node 9 .nil .nil)) =
    .node 40 (.node 0 .nil (.node 30 .nil .nil))
      (.node 5 (.node 50 .nil .nil) (.node 9 .nil .nil)) := by decide

/-- Weights count external leaves: `weight nil = 1` and the weight of a
node is the sum of the weights of its children. -/
example : weight (.nil : BinaryTree Nat) = 1 := rfl

example : weight (.node 2 (.node 1 .nil .nil) (.node 3 .nil .nil)) = 4 :=
  by decide

example (l r : BinaryTree Nat) (k : Nat) :
    weight (.node k l r) = weight l + weight r :=
  weight_node

/-- A four-key right spine is *not* `BB[1/4]`-balanced: its root's right
child has weight `4` out of total weight `5`, a ratio of `4 / 5 > 3 / 4`.
A key-count-only invariant would incorrectly accept this tree. -/
example : ¬ Balanced
    (.node 1 .nil (.node 2 .nil (.node 3 .nil (.node 4 .nil .nil))) :
      BinaryTree Nat) := by
  intro h
  obtain ⟨-, -, -, hRight⟩ := (balanced_node_iff_weight.mp h)
  simp only [weight_node, weight_empty] at hRight
  omega

/-- Consequently ascending insertion of four keys rotates instead of
leaving the four-key spine in place. -/
example : insList [1, 2, 3, 4] =
    .node 2 (.node 1 .nil .nil) (.node 3 .nil (.node 4 .nil .nil)) := by
  decide

example : BinaryTree.height (insList [1, 2, 3, 4]) = 3 := by decide

/-- The `Balanced` predicate for a node is exactly the classical weight
condition on its children. -/
example (l r : BinaryTree Nat) (k : Nat) :
    Balanced (.node k l r) ↔
      Balanced l ∧ Balanced r ∧
        4 * weight l ≤ 3 * weight (.node k l r) ∧
          4 * weight r ≤ 3 * weight (.node k l r) :=
  balanced_node_iff_weight

/-- Ascending insertion stays shallower only because rotations fire: an
unrotated chain of seven keys would have height `7`. -/
example : BinaryTree.height (insList [1, 2, 3, 4, 5, 6, 7]) = 5 := by decide

example : BinaryTree.height (insList [7, 6, 5, 4, 3, 2, 1]) = 5 := by decide

example : BinarySearchTree.inorder (insList [5, 3, 8, 1, 4, 3]) =
    [1, 3, 4, 5, 8] := by decide

example : BinarySearchTree.contains 4 (insList [5, 3, 8, 1, 4]) = true := by
  decide

example : BinarySearchTree.contains 6 (insList [5, 3, 8, 1, 4]) = false := by
  decide

example : (4 : Nat) ∈ insList [5, 3, 8, 1, 4] :=
  BinarySearchTree.mem_inorder.mp (by decide)

example (xs : List Nat) : Balanced (fromList xs) :=
  balanced_fromList

example (xs : List Nat) : BinarySearchTree.Ordered (fromList xs) :=
  ordered_fromList

example (x : Nat) (xs : List Nat) : x ∈ fromList xs ↔ x ∈ xs :=
  mem_fromList

example (t : BinaryTree Nat) (hBal : Balanced t) (x : Nat) :
    Balanced (insert x t) :=
  balanced_insert hBal

example (t : BinaryTree Nat) (hBal : Balanced t) :
    BinaryTree.height t ≤ Nat.log2 ((t.numNodes + 1) ^ 3) + 1 :=
  height_le_log2 hBal

example (l r : BinaryTree Nat) (k : Nat) :
    (balance l k r).numNodes = l.numNodes + r.numNodes + 1 :=
  numNodes_balance

#print axioms Cslib.Algorithms.Lean.WeightBalancedTree.balanced_insert
#print axioms Cslib.Algorithms.Lean.WeightBalancedTree.ordered_insert
#print axioms Cslib.Algorithms.Lean.WeightBalancedTree.mem_insert
#print axioms Cslib.Algorithms.Lean.WeightBalancedTree.height_le_log2
#print axioms Cslib.Algorithms.Lean.WeightBalancedTree.balanced_node_iff_weight
#print axioms Cslib.Algorithms.Lean.WeightBalancedTree.pow_height_le

end Cslib.Algorithms.Lean.WeightBalancedTreeTests
