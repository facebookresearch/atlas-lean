/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.PetersenColoring

open MathlibExt.GraphTheory.PetersenColoringConjectureWanted

-- Check wraparound on the two layers and distinguish spokes from cross-layer nonedges.
example :
    petersenGraph.Adj (4, false) (0, false) ∧
    petersenGraph.Adj (4, true) (1, true) ∧
    petersenGraph.Adj (2, false) (2, true) ∧
    ¬ petersenGraph.Adj (0, true) (1, true) ∧
    ¬ petersenGraph.Adj (2, false) (3, true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [petersenGraph, SimpleGraph.fromEdgeSet_adj, petersenEdgeSet,
      Set.mem_union, Set.mem_ofPred_eq] <;> decide

-- The identity realizes the full local bijection at each Petersen vertex.
example : IsPetersenColoring petersenGraph id :=
  ⟨fun _ he => he, fun v => ⟨v, Set.bijOn_id _⟩⟩

example : ¬ conjecture := conjecture_refuted
