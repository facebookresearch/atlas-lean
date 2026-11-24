/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.KirchhoffEffectiveResistance
import MathlibExt.Combinatorics.EndpointMapMultigraph.DartLaplacian
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for Kirchhoff's effective resistance formula -/

namespace MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted

open MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
open Matrix

/-- Every spanning tree of the graph with a single edge contains that edge. -/
example :
    (Nat.card {T : (⊤ : SimpleGraph (Fin 2)).Subgraph //
      IsSpanningTree T ∧ T.Adj 0 1} : ℝ) / numSpanningTrees (⊤ : SimpleGraph (Fin 2)) = 1 := by
  let G : SimpleGraph (Fin 2) := ⊤
  let f : Fin 2 → ℝ := ![1, 0]
  have huv : G.Adj 0 1 := by decide
  have hf : G.lapMatrix ℝ *ᵥ f = Pi.single 0 1 - Pi.single 1 1 := by
    funext x
    fin_cases x <;>
      norm_num [G, f, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, SimpleGraph.lapMatrix,
        SimpleGraph.adjMatrix_apply, SimpleGraph.top_adj, Pi.single_apply, Matrix.one_apply]
  rw [card_spanningTree_adj_div_numSpanningTrees G SimpleGraph.connected_top huv,
    (EndpointMapMultigraph.effectiveResistance_eq_sub_of_laplacian_mulVec _ _
      (fun _ => by norm_num) huv.ne
      (by rwa [EndpointMapMultigraph.laplacian_dart_eq_lapMatrix])).1]
  norm_num [f]

/-- An edge of the triangle lies in two thirds of its spanning trees. -/
example :
    (Nat.card {T : (⊤ : SimpleGraph (Fin 3)).Subgraph //
      IsSpanningTree T ∧ T.Adj 0 1} : ℝ) / numSpanningTrees (⊤ : SimpleGraph (Fin 3)) =
      2 / 3 := by
  let G : SimpleGraph (Fin 3) := ⊤
  let f : Fin 3 → ℝ := ![2 / 3, 0, 1 / 3]
  have huv : G.Adj 0 1 := by decide
  have hf : G.lapMatrix ℝ *ᵥ f = Pi.single 0 1 - Pi.single 1 1 := by
    funext x
    fin_cases x <;>
      norm_num [G, f, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, SimpleGraph.lapMatrix,
        SimpleGraph.adjMatrix_apply, SimpleGraph.top_adj, Pi.single_apply, Matrix.ofNat_apply]
  rw [card_spanningTree_adj_div_numSpanningTrees G SimpleGraph.connected_top huv,
    (EndpointMapMultigraph.effectiveResistance_eq_sub_of_laplacian_mulVec _ _
      (fun _ => by norm_num) huv.ne
      (by rwa [EndpointMapMultigraph.laplacian_dart_eq_lapMatrix])).1]
  norm_num [f]

end MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted
