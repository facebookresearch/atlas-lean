/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.TreewidthDuality
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace MathlibExtTest.Combinatorics.SimpleGraph.TreewidthDuality

open _root_.SimpleGraph MetaMathlibExt

-- The converse includes graphs with no vertices, even at the smallest width bound.
example (G : SimpleGraph (Fin 0)) : G.HasTreewidthAtMost 0 := by
  apply (hasTreewidthAtMost_iff_forall_bramble G 0).mpr
  exact fun _ hB => hB.not_orderGT_of_card_le G (by simp)

-- The threshold is sharp on the four-vertex complete graph.
example : ∃ (B : Set (Set (Fin 4))) (hB : (⊤ : SimpleGraph (Fin 4)).IsBramble B),
    hB.OrderGT 3 := by
  by_contra! h
  have hw := (hasTreewidthAtMost_iff_forall_bramble (⊤ : SimpleGraph (Fin 4)) 2).mpr h
  simpa using hasTreewidthAtMost_top_iff.mp hw

example (B : Set (Set (Fin 4))) (hB : (⊤ : SimpleGraph (Fin 4)).IsBramble B) :
    ¬hB.OrderGT 4 := by
  apply (hasTreewidthAtMost_iff_forall_bramble (⊤ : SimpleGraph (Fin 4)) 3).mp _ B hB
  exact hasTreewidthAtMost_top_iff.mpr (by simp)

-- A two-vertex cover suffices for every bramble in a path with five vertices.
example (B : Set (Set (Fin 5))) (hB : (pathGraph 5).IsBramble B) : ¬hB.OrderGT 2 :=
  (hasTreewidthAtMost_iff_forall_bramble (pathGraph 5) 1).mp
    ((isTree_pathGraph.mpr (by decide)).hasTreewidthAtMost_one) B hB

end MathlibExtTest.Combinatorics.SimpleGraph.TreewidthDuality
