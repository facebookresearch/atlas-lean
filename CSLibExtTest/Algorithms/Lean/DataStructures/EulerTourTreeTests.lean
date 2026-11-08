/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.EulerTourTree

/-!
# Tests for the Euler-tour-tree API

Client examples for leaf `cutLast`, multi-child tour ordering, link/cut
round trips, and the forest validity invariant through the public API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.EulerTourTreeTests

open Cslib.Algorithms.Lean EulerTourTree

public def leaf (r : Nat) : Tree Nat := .node r []

public def small : Tree Nat := .node 0 [leaf 1, leaf 2]

example : Tree.vertices small = [0, 1, 2] := by
  rw [small, Tree.vertices_node]
  simp [leaf, Tree.vertices_node]

/-- Multi-child tour ordering: root, first subtree, root, second, root. -/
example : Tree.tour small = [0, 1, 0, 2, 0] := by
  rw [small, Tree.tour_node]
  simp [leaf, Tree.tour_node]

example : Tree.tourAux small [9] = [0, 1, 0, 2, 0, 9] := by
  rw [Tree.tourAux_eq]
  have h : Tree.tour small = [0, 1, 0, 2, 0] := by
    rw [small, Tree.tour_node]
    simp [leaf, Tree.tour_node]
  rw [h]; rfl

example : Tree.arcTour small = [(0, 1), (1, 0), (0, 2), (2, 0)] := by
  rw [Tree.arcTour_eq_zip]
  have h : Tree.tour small = [0, 1, 0, 2, 0] := by
    rw [small, Tree.tour_node]
    simp [leaf, Tree.tour_node]
  rw [h]; rfl

example : (Tree.tour small).length = 5 := by
  rw [Tree.tour_length]
  simp [small, leaf, Tree.size]

/-- `cutLast` on a leaf has no last child to remove. -/
example : Tree.cutLast (leaf 7) = none := rfl

example : Tree.cutLast small = some (.node 0 [leaf 1], leaf 2) := by
  rw [small, Tree.cutLast]
  rfl

/-- Link/cut round trip through the public theorem. -/
example : Tree.cutLast (Tree.link small (leaf 3)) = some (small, leaf 3) :=
  Tree.cutLast_link small (leaf 3)

example : Tree.tour (Tree.link (leaf 0) (leaf 1)) = [0, 1, 0] := by
  rw [Tree.tour_link]
  simp [leaf, Tree.tour_node, Tree.root]

example : Tree.Valid small := by
  show Tree.Valid (.node 0 [leaf 1, leaf 2])
  rw [Tree.Valid, Tree.vertices_node]
  simp [leaf, Tree.vertices_node]

example : Tree.Valid (Tree.link (leaf 0) (leaf 1)) :=
  Tree.valid_link (Tree.valid_singleton 0) (Tree.valid_singleton 1) (by
    simp [leaf, Tree.vertices_node])

/-- The reviewer counterexample: same-root singletons do not form a forest link. -/
example : ¬ Tree.Valid (Tree.link (leaf 0) (leaf 0)) :=
  Tree.not_valid_link_same_root 0

example (t : Tree Nat) (v : Nat) : v ∈ Tree.tour t ↔ v ∈ Tree.vertices t :=
  Tree.mem_tour_iff t v

example (t₁ t₂ : Tree Nat) : Tree.size (Tree.link t₁ t₂) = Tree.size t₁ + Tree.size t₂ :=
  Tree.size_link t₁ t₂

#print axioms Tree.tour_link
#print axioms Tree.valid_link
#print axioms Tree.tourAux_eq
#print axioms Tree.verticesAux_eq

end Cslib.Algorithms.Lean.EulerTourTreeTests
