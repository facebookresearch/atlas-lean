/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeEight

namespace MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted

open _root_.SimpleGraph

-- Recover an actual four-cycle-free subgraph with the improved edge count from the maximum.
example : ∃ S : Subgraph (hypercubeGraph 8), (cycleGraph 4).Free S.coe ∧ 682 ≤ S.edgeSet.ncard := by
  have hne : cycleGraph 4 ≠ ⊥ := by
    intro h
    have h01 : (cycleGraph 4).Adj 0 1 := by decide
    rw [h] at h01
    exact h01
  obtain ⟨S, hfree, hcard⟩ := exists_attains_hypercubeTuranNumber 8
    ⟨(⊥ : Subgraph (hypercubeGraph 8)), by exact free_bot hne⟩
  exact ⟨S, hfree, hcard ▸ le_hypercubeTuranNumber_eight_cycleGraph_four⟩

end MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted
