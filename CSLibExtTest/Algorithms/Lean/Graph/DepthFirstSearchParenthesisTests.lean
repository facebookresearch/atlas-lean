/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DepthFirstSearchParenthesis
public meta import CSLibExt.Algorithms.Lean.Graph.DepthFirstSearch
public import Mathlib.Tactic.FinCases

/-!
# Tests for interval nesting and white paths in depth-first search

On the out-star `0 → 1`, `0 → 2` the search discovers `0, 1, 2` and finishes `1, 2, 0`: the
intervals of `1` and `2` are disjoint and both nest in that of `0`, matching the tree arcs.
The characterisations are instantiated on this graph.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DepthFirstSearchParenthesisTests

open DepthFirstSearch StronglyConnectedLowlink

/-- The out-star `0 → 1`, `0 → 2`. -/
def star : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by intro v; fin_cases v <;> simp
  adjacency := fun v => if v = 0 then [1, 2] else []

#guard (dfsAll star).preorder == [0, 1, 2]
#guard (dfsAll star).postorder == [1, 2, 0]
#guard (dfsAll star).parents == [(1, 0), (2, 0)]

example (u v : Fin 3) :
    TreeAncestor (dfsAll star).parents u v ↔
      (dfsAll star).preorder.idxOf u ≤ (dfsAll star).preorder.idxOf v ∧
        (dfsAll star).postorder.idxOf v ≤ (dfsAll star).postorder.idxOf u :=
  dfsAll_treeAncestor_iff star u v

example (u v : Fin 3) :
    TreeAncestor (dfsAll star).parents u v ↔
      Relation.ReflTransGen (fun x y => star.Edge x y ∧
        (dfsAll star).preorder.idxOf u ≤ (dfsAll star).preorder.idxOf y) u v :=
  dfsAll_treeAncestor_iff_whitePath star u v

end Cslib.Algorithms.Lean.DepthFirstSearchParenthesisTests
