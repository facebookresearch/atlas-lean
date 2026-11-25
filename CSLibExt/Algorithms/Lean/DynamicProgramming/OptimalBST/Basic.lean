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

/-- **Expected search cost of a binary search tree.** Let $R$ be an additive commutative monoid,
let $n$ be a natural number, and let $p_0, \dots, p_{n-1} \in R$ (key weights) and
$q_0, \dots, q_n \in R$ (dummy-key weights) be given. Let $T$ be a binary tree whose nodes are
labelled by elements of $\{0, \dots, n-1\}$ and whose inorder traversal is $0, 1, \dots, n-1$, so
each key labels exactly one node and $T$ has exactly $n + 1$ empty subtrees. The depth of a node
or empty subtree is its distance from the root, the root having depth $0$; write $d(k)$ for the
depth of the node labelled $k$ and $\ell_0, \dots, \ell_n$ for the depths of the empty subtrees
listed from left to right. The expected search cost of $T$ is
$$\sum_{k=0}^{n-1} (d(k) + 1) \cdot p_k + \sum_{i=0}^{n} (\ell_i + 1) \cdot q_i,$$
where $m \cdot x$ denotes the $m$-fold sum of $x$ in $R$. -/
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

/-- **Optimal binary search tree procedure.** Let $R$ be a linearly ordered additive commutative
monoid in which addition is monotone, let $n$ be a natural number, and let
$p_0, \dots, p_{n-1}, q_0, \dots, q_n \in R$. The procedure (CLRS OPTIMAL-BST, with keys indexed
from $0$) fills a cost table $e$ of size $(n+1) \times (n+1)$, an auxiliary weight table $w$ of
the same size, and a root table of size $n \times n$ with entries in $\{0, \dots, n-1\}$ or
empty; all entries start as $0$ or empty. First it sets $e[a][a] = w[a][a] = q_a$ for
$a = 0, \dots, n$. Then for $\ell = 1, \dots, n$ in increasing order and, for each $\ell$, for
$a = 0, \dots, n - \ell$ in increasing order, with $b = a + \ell$, it sets
$w[a][b] = w[a][b-1] + p_{b-1} + q_b$ and examines the candidate roots $r = a, \dots, b-1$ in
increasing order, replacing the current best only when the candidate value
$e[a][r] + e[r+1][b] + w[a][b]$ is strictly smaller. It stores the resulting minimum in $e[a][b]$
and the earliest minimizing $r$ at position $(a, b-1)$ of the root table. The procedure returns
the cost table $e$ and the root table, with running time equal to the total number of candidate
roots examined. -/
public def optimalBST [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) : TimeM Nat
    (Vector (Vector R (n + 1)) (n + 1) ×
      Vector (Vector (Option (Fin n)) n) n) :=
  let result := execute p q
  ⟨(result.1, result.2.2.1), result.2.2.2⟩

end Cslib.Algorithms.Lean.OptimalBST
