/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public meta import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.WithBot

public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat

/-!
# Optimal binary search trees

Source: CLRS, fourth edition, Section 14.5, pages 400-407 and Figure 14.10.
Keys are indexed by `Fin n`. The table interval `[a,b)` includes keys `a` through
`b-1` and every dummy key from `a` through `b`. The objective includes all successful
keys and all `n+1` unsuccessful dummies, using a proof-only complete inorder.
The sole executor visits ascending lengths, starts, and candidate roots. Strict
improvement retains the earliest root on ties. Ordered additive inputs extend the
source's nonnegative real probabilities without changing the executed recurrence.
-/

set_option autoImplicit false
universe u

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BinarySearchTree
open scoped BigOperators

namespace Cslib.Algorithms.Lean.OptimalBST

variable {R : Type u}

private def keyCost [AddCommMonoid R] {n : Nat} (p : Vector R n) :
    Nat → BinaryTree (Fin n) → R
  | _, .nil => 0
  | depth, .node key left right =>
      (depth + 1) • p[key.val] + keyCost p (depth + 1) left +
        keyCost p (depth + 1) right

private def dummyDepths {n : Nat} : BinaryTree (Fin n) → Nat → List Nat
  | .nil, depth => [depth]
  | .node _ left right, depth =>
      dummyDepths left (depth + 1) ++ dummyDepths right (depth + 1)

private theorem dummyDepths_length {n : Nat} (tree : BinaryTree (Fin n))
    (depth : Nat) : (dummyDepths tree depth).length = tree.numLeaves := by
  induction tree generalizing depth with
  | nil => rfl
  | node key left right ihLeft ihRight =>
    simp [dummyDepths, ihLeft, ihRight]

/-- CLRS search cost, including every successful key and every unsuccessful dummy. -/
public def expectedSearchCost [AddCommMonoid R] (n : Nat)
    (p : Vector R n) (q : Vector R (n + 1))
    (tree : BinaryTree (Fin n))
    (complete : inorder tree = List.finRange n) : R :=
  let depths := dummyDepths tree 0
  have nodes : tree.numNodes = n := by
    rw [numNodes_eq_length_inorder, complete]
    simp
  have leaves : tree.numLeaves = n + 1 := by
    rw [BinaryTree.numLeaves_eq_numNodes_succ, nodes]
  have depthCount : depths.length = n + 1 := by
    rw [dummyDepths_length, leaves]
  let depthVector : Vector Nat (n + 1) :=
    ⟨depths.toArray, by simp [depthCount]⟩
  keyCost p 0 tree +
    ∑ i : Fin (n + 1), (depthVector[i.val] + 1) • q[i.val]

private def execute [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) :
    Vector (Vector R (n + 1)) (n + 1) ×
      Vector (Vector R (n + 1)) (n + 1) ×
      Vector (Vector (Option (Fin n)) n) n × Nat := Id.run do
  let mut e := Vector.replicate (n + 1) (Vector.replicate (n + 1) (0 : R))
  let mut w := Vector.replicate (n + 1) (Vector.replicate (n + 1) (0 : R))
  let mut root := Vector.replicate n (Vector.replicate n (none : Option (Fin n)))
  let mut candidateCount : Nat := 0
  for hi : i in [:n + 1] do
    e := e.set i (e[i].set i q[i])
    w := w.set i (w[i].set i q[i])
  for hl : lengthOffset in [:n] do
    have hLengthOffset : lengthOffset < n := hl.2.1
    let length := lengthOffset + 1
    for ha : a in [:n - length + 1] do
      have hStart : a < n - length + 1 := ha.2.1
      let b := a + length
      have hB : b ≤ n := by omega
      have hA : a < n := by omega
      let savedWeight := w[a][b - 1] + p[b - 1] + q[b]
      w := w.set a (w[a].set b savedWeight)
      let firstRoot : Fin n := ⟨a, hA⟩
      let firstCandidate := e[a][a] + e[a + 1][b] + savedWeight
      let initialBest : WithTop R :=
        if (firstCandidate : WithTop R) < ⊤ then firstCandidate else ⊤
      have finiteInitial : initialBest ≠ ⊤ := by
        simp [initialBest]
      let mut best := initialBest.untop finiteInitial
      let mut chosen := firstRoot
      candidateCount := candidateCount + 1
      for hr : rootOffset in [:length - 1] do
        have hRootOffset : rootOffset < length - 1 := hr.2.1
        let rootIndex := a + rootOffset + 1
        have hRoot : rootIndex < n := by omega
        have hLeft : rootIndex < n + 1 := by omega
        have hRight : rootIndex + 1 < n + 1 := by omega
        let candidate := e[a][rootIndex] + e[rootIndex + 1][b] + savedWeight
        if candidate < best then
          best := candidate
          chosen := ⟨rootIndex, hRoot⟩
        candidateCount := candidateCount + 1
      e := e.set a (e[a].set b best)
      root := root.set a (root[a].set (b - 1) (some chosen))
  return (e, w, root, candidateCount)

/-- CLRS OPTIMAL-BST with saved `e`, saved `w`, saved earliest roots, and candidate-event time. -/
public def optimalBST [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) : TimeM Nat
    (Vector (Vector R (n + 1)) (n + 1) ×
      Vector (Vector (Option (Fin n)) n) n) :=
  let result := execute p q
  ⟨(result.1, result.2.2.1), result.2.2.2⟩

end Cslib.Algorithms.Lean.OptimalBST
