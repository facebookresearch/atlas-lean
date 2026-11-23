/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.CutRank
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.CutRank

open _root_.SimpleGraph

-- Local complementation at the middle vertex of the path 0 - 1 - 2 adds the edge 02.
example : ((pathGraph 3).localComplement 1).Adj 0 2 := by
  rw [localComplement_adj]
  simp [pathGraph_adj]

-- Local complementation at an end vertex of the path changes nothing: 0 has one neighbour.
example : ¬((pathGraph 3).localComplement 0).Adj 0 2 := by
  rw [localComplement_adj]
  simp [pathGraph_adj]

-- ... and the edge 01 survives local complementation at 0.
example : ((pathGraph 3).localComplement 0).Adj 0 1 := by
  rw [localComplement_adj_left]
  simp [pathGraph_adj]

-- Involution.
example (G : SimpleGraph (Fin 4)) (v : Fin 4) :
    (G.localComplement v).localComplement v = G :=
  localComplement_localComplement G v

-- The edgeless graph has cut-rank zero everywhere: its cut matrices vanish.
example (X : Set (Fin 3)) : (⊥ : SimpleGraph (Fin 3)).cutRank X = 0 := by
  classical
  unfold cutRank
  convert Matrix.rank_zero (R := ZMod 2) using 2
  all_goals first
    | (ext x y; simp)
    | infer_instance

-- Symmetry and invariance under local complementation, on a concrete graph.
example (X : Set (Fin 3)) :
    ((pathGraph 3).localComplement 1).cutRank Xᶜ = (pathGraph 3).cutRank X := by
  rw [cutRank_compl, cutRank_localComplement]

-- Complete graphs have cut-rank at most one.
example (X : Set (Fin 5)) : (⊤ : SimpleGraph (Fin 5)).cutRank X ≤ 1 := cutRank_top_le_one X

-- Two local complementations give a locally equivalent graph, which is locally equivalent back.
example (G : SimpleGraph (Fin 4)) :
    ((G.localComplement 0).localComplement 2).LocallyEquivalent G := by
  apply LocallyEquivalent.symm
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨0, rfl⟩) ⟨2, rfl⟩

-- Vertex-minors: the graph itself and its local complements.
example (G : SimpleGraph (Fin 4)) : G.IsVertexMinor G := IsVertexMinor.refl G
example (G : SimpleGraph (Fin 4)) : (G.localComplement 3).IsVertexMinor G :=
  isVertexMinor_localComplement G 3

end MathlibExtTest.Combinatorics.SimpleGraph.CutRank
