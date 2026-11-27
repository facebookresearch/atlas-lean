/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeSevenLower

namespace MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted

open _root_.SimpleGraph

-- Recover exactly 304 edges, even if a maximizing subgraph has more.
example : ∃ S : Subgraph (hypercubeGraph 7), (cycleGraph 4).Free S.coe ∧ S.edgeSet.ncard = 304 := by
  have hne : cycleGraph 4 ≠ ⊥ := by
    intro h
    have h01 : (cycleGraph 4).Adj 0 1 := by decide
    rw [h] at h01
    exact h01
  obtain ⟨S, hfree, hcard⟩ := exists_attains_hypercubeTuranNumber 7
    ⟨(⊥ : Subgraph (hypercubeGraph 7)), free_bot hne⟩
  have hle : 304 ≤ S.edgeSet.ncard := hcard ▸ le_hypercubeTuranNumber_seven_cycleGraph_four
  obtain ⟨E, hE, hsize⟩ := Set.exists_subset_card_eq hle
  refine ⟨S.deleteEdges (S.edgeSet \ E), ?_, ?_⟩
  · exact fun h => hfree (h.mono_right (Subgraph.coe_deleteEdges_le _))
  · rw [← Subgraph.edgeSet_spanningCoe, ← Subgraph.deleteEdges_spanningCoe_eq, edgeSet_deleteEdges,
      Subgraph.edgeSet_spanningCoe, sdiff_sdiff_eq_self hE, hsize]

end MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted
