/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.EulerTourTree.Depth

/-!
# Tests for depth-annotated Euler tours

Client examples for `Tree.depthTour` on a tree whose root has two children,
the first of which has a child of its own: the complete annotated sequence,
the return to the parent between siblings, sibling depths, the accumulator
form, the projection to `Tree.tour`, and the entry count.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.EulerTourTree.DepthTests

open Cslib.Algorithms.Lean EulerTourTree

/-- A leaf with root `r`. -/
public def leaf (r : Nat) : Tree Nat := .node r []

/-- Root `0` with children `1` and `2`, where `1` has the child `3`. -/
public def nested : Tree Nat := .node 0 [.node 1 [leaf 3], leaf 2]

/-- A single vertex is recorded once, at the starting depth. -/
example : Tree.depthTour 5 (leaf 7) = [(7, 5)] := by
  simp [leaf, Tree.depthTour_node]

/-- The complete annotated sequence: after the nested subtree of `1` the walk
returns to the root at depth `0`, and the sibling `2` starts at depth `1`,
the depth of its sibling `1`. -/
example : Tree.depthTour 0 nested =
    [(0, 0), (1, 1), (3, 2), (1, 1), (0, 0), (2, 1), (0, 0)] := by
  simp [nested, leaf, Tree.depthTour_node]

/-- Starting at depth `2` shifts every depth by `2`. -/
example : Tree.depthTour 2 nested =
    [(0, 2), (1, 3), (3, 4), (1, 3), (0, 2), (2, 3), (0, 2)] := by
  simp [nested, leaf, Tree.depthTour_node]

/-- Siblings `1` and `2` are entered at the same depth, the root's depth plus
one, with the root re-emitted at its own depth between them. -/
example : (Tree.depthTour 0 nested)[1]? = some (1, 1) ∧
    (Tree.depthTour 0 nested)[4]? = some (0, 0) ∧
    (Tree.depthTour 0 nested)[5]? = some (2, 1) := by
  simp [nested, leaf, Tree.depthTour_node]

/-- The accumulator form appends the tour onto the accumulator. -/
example : Tree.depthTourAux nested 0 [(9, 0)] =
    [(0, 0), (1, 1), (3, 2), (1, 1), (0, 0), (2, 1), (0, 0), (9, 0)] := by
  rw [Tree.depthTourAux_eq]
  simp [nested, leaf, Tree.depthTour_node]

/-- Forgetting depths gives the Euler tour of `Tree.tour`. -/
example : (Tree.depthTour 0 nested).map Prod.fst = Tree.tour nested :=
  Tree.map_fst_depthTour 0 nested

example : Tree.tour nested = [0, 1, 3, 1, 0, 2, 0] := by
  rw [← Tree.map_fst_depthTour 0 nested]
  simp [nested, leaf, Tree.depthTour_node]

/-- Four vertices give `2 * 4 - 1 = 7` entries. -/
example : (Tree.depthTour 0 nested).length = 7 := by
  have h := Tree.depthTour_length_add_one 0 nested
  have hs : Tree.size nested = 4 := by simp [nested, leaf, Tree.size]
  omega

end Cslib.Algorithms.Lean.EulerTourTree.DepthTests
