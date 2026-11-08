/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BallTree
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Tests for the ball-tree API

These client examples exercise distance, construction, validity, and
pruning search through the public executable and correctness API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BallTreeTests

open BallTree

public def origin : Fin 2 → Int := ![0, 0]

public def far : Fin 2 → Int := ![10, 0]

public theorem dist_origin_far : distSq origin far = 100 := by
  norm_num [distSq, origin, far, Fin.sum_univ_two]

public theorem dist_origin_origin : distSq origin origin = 0 := by
  norm_num [distSq, origin, Fin.sum_univ_two]

example : distSq far origin = distSq origin far :=
  distSq_comm _ _

example : (BallTree.empty : BallTree 2).toList = [] := rfl

example : (BallTree.empty : BallTree 2).search origin 100 = [] := rfl

example : (BallTree.leaf origin).search origin 0 = [origin] := by
  simp [search, searchAux, dist_origin_origin]

example : (BallTree.leaf far).search origin 5 = [] := by
  simp [search, searchAux, dist_origin_far]

public def tree : BallTree 2 :=
  .node origin 100 (.leaf origin) (.leaf far)

example : tree.toList = [origin, far] := by
  simp [tree, toList_node]

public theorem tree_valid : tree.Valid := by
  refine Valid.node (center := origin) (bound := 100)
    (left := .leaf origin) (right := .leaf far)
    (Valid.leaf origin) (Valid.leaf far) ?_ ?_
  · intro p hp
    simp only [toList_leaf, List.mem_singleton] at hp
    rw [hp, dist_origin_origin]
    exact Nat.zero_le _
  · intro p hp
    simp only [toList_leaf, List.mem_singleton] at hp
    rw [hp, dist_origin_far]

example : tree.search origin 5 = [origin] := by
  rw [search_eq_filter tree_valid]
  simp [tree, toList_node, dist_origin_origin, dist_origin_far]

example : far ∈ tree.search origin 100 := by
  rw [mem_search_iff tree_valid]
  exact ⟨by simp [tree, toList_node], by rw [dist_origin_far]⟩

example (pts : List (Fin 2 → Int)) : (build pts).Valid :=
  valid_build pts

example (pts : List (Fin 2 → Int)) : (build pts).size = pts.length :=
  size_build pts

example (pts : List (Fin 2 → Int)) (p : Fin 2 → Int) :
    p ∈ (build pts).search origin 100 ↔
      p ∈ pts ∧ distSq origin p ≤ 100 :=
  mem_search_build_iff pts

example : radiusSq origin [origin, far] = 100 := by
  simp [radiusSq, dist_origin_origin, dist_origin_far]

example : distSq origin far ≤ radiusSq origin [origin, far] :=
  distSq_le_radiusSq (by simp)

#print axioms Cslib.Algorithms.Lean.BallTree.search_eq_filter
#print axioms Cslib.Algorithms.Lean.BallTree.valid_build
#print axioms Cslib.Algorithms.Lean.BallTree.mem_search_build_iff
#print axioms Cslib.Algorithms.Lean.BallTree.distSq_le_two_mul

end Cslib.Algorithms.Lean.BallTreeTests
