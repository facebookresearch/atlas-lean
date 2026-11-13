/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexFKFiniteWiredCofinal
import Code.BeffaraDC.PlanarFKDuality








open SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice BeffaraDC


def hexagonalBrickVertex (u : HexVertex) : Site 2 :=
  if u.2 then
    ![2 * u.1 0 + u.1 1 - 2, -u.1 1 + 1]
  else
    ![2 * u.1 0 + u.1 1, -u.1 1]

theorem hexagonalBrickVertex_injective :
    Function.Injective hexagonalBrickVertex := by
  rintro ⟨x, bx⟩ ⟨y, cy⟩ h
  cases bx <;> cases cy <;>
    simp [hexagonalBrickVertex, funext_iff] at h ⊢ <;> omega


theorem hexagonalBrickVertex_adj {u v : HexVertex}
    (huv : hexagonalGraph.Adj u v) :
    (hypercubicLattice 2).Adj
      (hexagonalBrickVertex u) (hexagonalBrickVertex v) := by
  rw [hexagonalGraph_adj] at huv
  rcases u with ⟨x, bx⟩
  rcases v with ⟨y, cy⟩
  rcases huv with ⟨rfl, rfl, i, hi⟩ | ⟨rfl, rfl, i, hi⟩ <;>
    rw [hypercubicLattice_adj] <;>
    fin_cases i <;>
    simp [hexagonalBrickVertex, hexagonalStep, funext_iff] at hi ⊢ <;>
    omega


def hexagonalBrickEmbedding : HexVertex ↪ Site 2 where
  toFun := hexagonalBrickVertex
  inj' := hexagonalBrickVertex_injective


def triHexPlanarFiniteStarBrickEmbedding (n : Nat) :
    TriHexPlanarFiniteStarVertex n ↪ Site 2 :=
  (triHexPlanarFiniteStarVertexEmbedding n).trans hexagonalBrickEmbedding


noncomputable def triHexPlanarFiniteStarPlanar (n : Nat) :
    PlanarZ2Subgraph where
  V := TriHexPlanarFiniteStarVertex n
  finV := inferInstance
  decV := inferInstance
  G := triHexPlanarFiniteStarGraph n
  emb := triHexPlanarFiniteStarBrickEmbedding n
  isSub := by
    intro u v huv
    exact hexagonalBrickVertex_adj
      (triHexPlanarFiniteStarGraph_adj_hexagonal n huv)

@[simp] theorem triHexPlanarFiniteStarPlanar_graph (n : Nat) :
    (triHexPlanarFiniteStarPlanar n).G =
      triHexPlanarFiniteStarGraph n := rfl

end StatMech.FK.PeriodicPlanar
