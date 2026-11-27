/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.TreewidthMinor

namespace MathlibExtTest.Combinatorics.Graph.TreewidthMinor

open MetaMathlibExt SimpleGraph

private abbrev path (n : ℕ) : FinGraph := ⟨Fin n, pathGraph n⟩

private def contractMiddle : Fin 4 → Fin 3
  | 0 => 0
  | 3 => 2
  | _ => 1

-- Contract the middle edge of the four-vertex path and pass its width bound to the minor.
example : (pathGraph 3).HasTreewidthAtMost 1 := by
  have step : MinorStep (path 3) (path 4) :=
    .contractEdge _ _ contractMiddle (by unfold Function.Surjective; decide)
      1 2 (by decide) (by decide) rfl (by decide) (by decide)
  exact (IsMinor.of_step step).hasTreewidthAtMost
    (isTree_pathGraph_add_one 3).hasTreewidthAtMost_one

-- A triangle minor rules out tree-width at most one.
example {G : FinGraph} (h : IsMinor (cliqueFinGraph 3) G) : ¬G.G.HasTreewidthAtMost 1 := by
  intro hG
  have hK : (⊤ : SimpleGraph (Fin 3)).HasTreewidthAtMost 1 := h.hasTreewidthAtMost hG
  have := hasTreewidthAtMost_top_iff.mp hK
  simp at this

end MathlibExtTest.Combinatorics.Graph.TreewidthMinor
