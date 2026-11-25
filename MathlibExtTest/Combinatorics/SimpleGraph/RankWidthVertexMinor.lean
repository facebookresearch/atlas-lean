/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RankWidthVertexMinor

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.RankWidthVertexMinor

open _root_.SimpleGraph

-- A local complement is a vertex-minor, so it inherits a rank-width bound.
example (G : SimpleGraph (Fin 4)) (h : G.HasRankWidthAtMost 1) :
    (G.localComplement 0).HasRankWidthAtMost 1 :=
  (isVertexMinor_localComplement G 0).hasRankWidthAtMost h

-- A graph reindexed along an injective map is a vertex-minor (an induced subgraph),
-- so it inherits a rank-width bound.
example (G : SimpleGraph (Fin 4)) (h : G.HasRankWidthAtMost 1) :
    (G.comap (⟨Fin.succ, Fin.succ_injective 3⟩ : Fin 3 ↪ Fin 4)).HasRankWidthAtMost 1 := by
  have hminor : (G.comap (⟨Fin.succ, Fin.succ_injective 3⟩ : Fin 3 ↪ Fin 4)).IsVertexMinor G :=
    ⟨G, Relation.ReflTransGen.refl, (⟨Fin.succ, Fin.succ_injective 3⟩ : Fin 3 ↪ Fin 4), rfl⟩
  exact hminor.hasRankWidthAtMost h

-- Every graph is a vertex-minor of itself, so the bound is preserved trivially.
example (G : SimpleGraph (Fin 4)) (h : G.HasRankWidthAtMost 2) :
    G.HasRankWidthAtMost 2 :=
  (IsVertexMinor.refl G).hasRankWidthAtMost h

end MathlibExtTest.Combinatorics.SimpleGraph.RankWidthVertexMinor
