/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DepthFirstSearchCosts

import Std.Data.HashSet.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Cslib.Algorithms.Lean.DepthFirstSearchCostsTests

open DepthFirstSearch
open DepthFirstSearch.Internal

attribute [local simp] Std.HashSet.not_mem_empty Std.HashSet.mem_insert

private def selfLoopGraph : DirectedAdjacency (Fin 1) where
  vertices := List.finRange 1
  vertices_nodup := List.nodup_finRange 1
  vertices_complete := List.mem_finRange
  adjacency _ := [0]

example : ∃ final : Machine (Fin 1), final.work = [] ∧
    finish final = dfs selfLoopGraph [0] ∧
    Relation.RelatesInSteps (Step selfLoopGraph [0]) (initial [0]) final 3 := by
  simpa [dfs, loop, initial, finish, enterFrames, selfLoopGraph] using
    dfs_exact_steps selfLoopGraph [0]

#print axioms Cslib.Algorithms.Lean.DepthFirstSearch.dfs_exact_steps

private def isolatedGraph (n : Nat) : DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency _ := []

example (n : Nat) : ∃ final : Machine (Fin n), final.work = [] ∧
    finish final = dfsAll (isolatedGraph n) ∧
    Relation.RelatesInSteps
      (Step (isolatedGraph n) (isolatedGraph n).vertices)
      (initial (isolatedGraph n).vertices) final (2 * n) := by
  simpa [isolatedGraph] using dfsAll_exact_steps (isolatedGraph n)

private def repeatedLoopGraph (k : Nat) : DirectedAdjacency (Fin 1) where
  vertices := List.finRange 1
  vertices_nodup := List.nodup_finRange 1
  vertices_complete := List.mem_finRange
  adjacency _ := List.replicate k 0

example (k : Nat) : ∃ final : Machine (Fin 1), final.work = [] ∧
    finish final = dfsAll (repeatedLoopGraph k) ∧
    Relation.RelatesInSteps
      (Step (repeatedLoopGraph k) (repeatedLoopGraph k).vertices)
      (initial (repeatedLoopGraph k).vertices) final (2 + k) := by
  simpa [repeatedLoopGraph] using dfsAll_exact_steps (repeatedLoopGraph k)

end Cslib.Algorithms.Lean.DepthFirstSearchCostsTests
