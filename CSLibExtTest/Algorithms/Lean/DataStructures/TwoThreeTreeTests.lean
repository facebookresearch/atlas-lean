/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.TwoThreeTree
public import Mathlib.Data.Nat.Basic

/-!
# Tests for the 2-3 tree API

Client examples exercise the linear `flattenAux` traversal and its node
equations, search hits and misses, duplicate insertion, and insertions
that split in the left, middle, and right children, through both the
height-indexed API and the existential-height `Root` API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TwoThreeTreeTests

open TwoThreeTree

private def twoNode : Tree Nat 1 := .node2 5 .leaf .leaf

private def threeNode : Tree Nat 1 := .node3 3 7 .leaf .leaf .leaf

example : flatten (Tree.leaf : Tree Nat 0) = [] := flatten_leaf

example : flatten twoNode = [5] := by
  simp [twoNode]

example : flatten threeNode = [3, 7] := by
  simp [threeNode]

example {h : Nat} {a : Nat} {l r : Tree Nat h} :
    flatten (.node2 a l r) = flatten l ++ a :: flatten r :=
  flatten_node2

example {h : Nat} {a b : Nat} {l m r : Tree Nat h} :
    flatten (.node3 a b l m r) =
      flatten l ++ a :: (flatten m ++ b :: flatten r) :=
  flatten_node3

/-- The accumulator traversal prepends the flattening to any suffix,
which is what makes `flatten` linear. -/
example {h : Nat} (t : Tree Nat h) (suffix : List Nat) :
    flattenAux t suffix = flatten t ++ suffix :=
  flattenAux_eq t suffix

example : flattenAux threeNode [9] = [3, 7, 9] := by
  rw [flattenAux_eq]
  simp [threeNode]

example : height twoNode = 1 := height_eq _

example : Balanced threeNode := balanced _

example : (5 : Nat) ∈ flatten twoNode := by
  simp [twoNode]

example : (4 : Nat) ∉ flatten twoNode := by
  simp [twoNode]

example {h : Nat} {x : Nat} {t : Tree Nat h} :
    x ∈ flatten t ↔ x ∈ t :=
  mem_flatten

example : Ordered twoNode := by
  simp [twoNode, Ordered, All]

example : Ordered threeNode := by
  simp [threeNode, Ordered, All]

example : contains 5 twoNode = true := by
  decide

example : contains 4 twoNode = false := by
  decide

example : contains 3 threeNode = true := by
  decide

example : contains 7 threeNode = true := by
  decide

example : contains 5 threeNode = false := by
  decide

example : List.Pairwise (· < ·) (flatten threeNode) :=
  ordered_flatten_pairwise (by simp [threeNode, Ordered, All])

example : (flatten threeNode).Nodup :=
  flatten_nodup (by simp [threeNode, Ordered, All])

/-- Inserting into a leaf splits around the new key. -/
example : ins 2 (Tree.leaf : Tree Nat 0) = .split .leaf 2 .leaf := by
  rfl

/-- A left split is absorbed by a 2-node, which becomes a 3-node. -/
example : ins 1 twoNode = .ok (.node3 1 5 .leaf .leaf .leaf) := by
  rfl

/-- A right split is absorbed by a 2-node, which becomes a 3-node. -/
example : ins 9 twoNode = .ok (.node3 5 9 .leaf .leaf .leaf) := by
  rfl

/-- Inserting a present separator is a no-op. -/
example : ins 5 twoNode = .ok twoNode := by
  rfl

/-- A left split under a 3-node propagates upward as a split. -/
example :
    ins 1 threeNode =
      .split (.node2 1 .leaf .leaf) 3 (.node2 7 .leaf .leaf) := by
  rfl

/-- A middle split under a 3-node propagates upward as a split. -/
example :
    ins 5 threeNode =
      .split (.node2 3 .leaf .leaf) 5 (.node2 7 .leaf .leaf) := by
  rfl

/-- A right split under a 3-node propagates upward as a split. -/
example :
    ins 9 threeNode =
      .split (.node2 3 .leaf .leaf) 7 (.node2 9 .leaf .leaf) := by
  rfl

example : ins 3 threeNode = .ok threeNode := by
  rfl

example : ins 7 threeNode = .ok threeNode := by
  rfl

example (x : Nat) {h : Nat} (t : Tree Nat h) (hOrd : Ordered t) :
    InsSpec x t (ins x t) :=
  ins_spec x t hOrd

example : (Root.empty : Root Nat).flatten = [] := Root.flatten_empty

example : (Root.empty : Root Nat).Ordered := Root.ordered_empty

example : (Root.fromList [3, 1, 2] : Root Nat).flatten = [1, 2, 3] := by
  decide

example :
    (Root.fromList [5, 4, 3, 2, 1] : Root Nat).flatten = [1, 2, 3, 4, 5] := by
  decide

example :
    (Root.fromList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : Root Nat).flatten =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  decide

/-- Duplicate keys in the input list produce one flattening entry. -/
example : (Root.fromList [2, 2, 1, 2] : Root Nat).flatten = [1, 2] := by
  decide

example (xs : List Nat) : (Root.fromList xs : Root Nat).Ordered :=
  Root.ordered_fromList xs

example {x : Nat} {xs : List Nat} :
    x ∈ (Root.fromList xs : Root Nat).flatten ↔ x ∈ xs :=
  Root.mem_fromList

example : (Root.fromList [3, 1, 2] : Root Nat).contains 2 = true := by
  decide

example : (Root.fromList [3, 1, 2] : Root Nat).contains 4 = false := by
  decide

example {x : Nat} {xs : List Nat} :
    (Root.fromList xs : Root Nat).contains x = true ↔
      x ∈ (Root.fromList xs : Root Nat).flatten :=
  Root.contains_eq_true_iff (Root.ordered_fromList xs)

example (x : Nat) (t : Root Nat) : (t.insert x).height ≤ t.height + 1 :=
  Root.height_insert_le x t

example (t : Root Nat) : TwoThreeTree.height t.tree = t.height :=
  Root.height_tree t

example (t : Root Nat) : Balanced t.tree := Root.balanced t

example {x y : Nat} {t : Root Nat} (hOrd : t.Ordered) :
    y ∈ (t.insert x).flatten ↔ y = x ∨ y ∈ t.flatten :=
  Root.mem_flatten_insert hOrd

example {x : Nat} {t : Root Nat} (hOrd : t.Ordered) :
    (t.insert x).flatten = orderedInsert x t.flatten :=
  Root.flatten_insert hOrd

#check TwoThreeTree.Tree
#check TwoThreeTree.flattenAux
#check TwoThreeTree.flatten
#check TwoThreeTree.flattenAux_eq
#check TwoThreeTree.contains
#check TwoThreeTree.ins
#check TwoThreeTree.ins_spec
#check TwoThreeTree.Root.insert
#check TwoThreeTree.Root.fromList
#check TwoThreeTree.Root.flatten_insert
#check TwoThreeTree.Root.ordered_fromList
#check TwoThreeTree.Root.mem_fromList

#print axioms TwoThreeTree.flattenAux_eq
#print axioms TwoThreeTree.flatten_node2
#print axioms TwoThreeTree.flatten_node3
#print axioms TwoThreeTree.mem_flatten
#print axioms TwoThreeTree.ordered_flatten_pairwise
#print axioms TwoThreeTree.flatten_nodup
#print axioms TwoThreeTree.contains_eq_true_iff
#print axioms TwoThreeTree.ins_spec
#print axioms TwoThreeTree.Root.ordered_insert
#print axioms TwoThreeTree.Root.flatten_insert
#print axioms TwoThreeTree.Root.mem_flatten_insert
#print axioms TwoThreeTree.Root.contains_eq_true_iff
#print axioms TwoThreeTree.Root.ordered_fromList
#print axioms TwoThreeTree.Root.mem_fromList

end Cslib.Algorithms.Lean.TwoThreeTreeTests
