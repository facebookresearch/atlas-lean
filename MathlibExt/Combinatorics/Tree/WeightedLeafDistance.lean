/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Weighted leaf-pair distances on binary trees

Record both edge length and edge count along paths between leaves. The latter determines
a topology-dependent linear functional on a dissimilarity matrix (Pauplin, 2000).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution

universe u

/-- A rooted binary tree with leaf labels in `X`; `node a l b r` has the child `l` at the end of
an edge of length `a` and the child `r` at the end of an edge of length `b`. -/
inductive RTree (X : Type u) where
  /-- A leaf with label `x`. -/
  | leaf : X → RTree X
  /-- An internal vertex with children `l` and `r` on edges of lengths `a` and `b`. -/
  | node : ℝ → RTree X → ℝ → RTree X → RTree X

/-- An unrooted binary tree, rooted at its edge of length `len` that joins the roots of the
rooted binary trees `left` and `right`. -/
structure UTree (X : Type u) where
  /-- The subtree on one side of the root edge. -/
  left : RTree X
  /-- The length of the root edge. -/
  len : ℝ
  /-- The subtree on the other side of the root edge. -/
  right : RTree X

variable {X : Type u}

/-- The Pauplin coefficient `2 ^ (1 - τ)` of a pair of leaves at topological distance `τ`. -/
noncomputable def pauplinCoeff (τ : ℕ) : ℝ :=
  2 / 2 ^ τ

namespace RTree

/-- The leaves, each with its label, its distance to the root and its number of edges to the
root. -/
def leaves : RTree X → List (X × ℝ × ℕ)
  | leaf x => [(x, 0, 0)]
  | node a l b r =>
    (leaves l).map (fun p => (p.1, p.2.1 + a, p.2.2 + 1)) ++
      (leaves r).map (fun p => (p.1, p.2.1 + b, p.2.2 + 1))

/-- The unordered pairs of leaves, each with the two labels, the length of the path between the
two leaves and its number of edges. -/
def pairs : RTree X → List (X × X × ℝ × ℕ)
  | leaf _ => []
  | node a l b r =>
    pairs l ++ pairs r ++
      (leaves l).flatMap fun p =>
        (leaves r).map fun q => (p.1, q.1, p.2.1 + a + b + q.2.1, p.2.2 + q.2.2 + 2)

end RTree

namespace UTree

/-- The leaf labels (with multiplicity). -/
def labels (T : UTree X) : List X :=
  T.left.leaves.map Prod.fst ++ T.right.leaves.map Prod.fst

/-- The unordered pairs of leaves, each with the two labels, the length `d_T(i, j)` of the path
between the two leaves and its number of edges `τ_ij`. -/
def pairs (T : UTree X) : List (X × X × ℝ × ℕ) :=
  T.left.pairs ++ T.right.pairs ++
    T.left.leaves.flatMap fun p =>
      T.right.leaves.map fun q => (p.1, q.1, p.2.1 + T.len + q.2.1, p.2.2 + q.2.2 + 1)

/-- The **balanced minimum-evolution length** of the topology of `T` for a dissimilarity `d`
(Desper and Gascuel 2002): `∑_{i<j} 2^{1-τ_ij} (d(i, j) + d(j, i)) / 2`. It depends on `T`
only through the topological distances `τ_ij`. Each term is symmetrized, so the value does
not depend on the orientation `T.pairs` happens to assign to a pair: swapping the children of
a node, or the two sides of the root edge, leaves `bmeLength` unchanged. -/
noncomputable def bmeLength (T : UTree X) (d : X → X → ℝ) : ℝ :=
  (T.pairs.map fun p => pauplinCoeff p.2.2.2 * (d p.1 p.2.1 + d p.2.1 p.1) / 2).sum

end UTree

end MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution
