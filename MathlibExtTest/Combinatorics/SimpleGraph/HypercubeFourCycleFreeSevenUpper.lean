/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeSevenUpper

namespace MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted

open _root_.SimpleGraph

-- One edge beyond the bound forces a copy, even when the subgraph is not spanning.
example (S : Subgraph (hypercubeGraph 7)) (h : 309 ≤ S.edgeSet.ncard) : (cycleGraph 4) ⊑ S.coe := by
  by_contra hfree
  have := (le_hypercubeTuranNumber 7 S hfree).trans hypercubeTuranNumber_seven_cycleGraph_four_le
  omega

end MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted
