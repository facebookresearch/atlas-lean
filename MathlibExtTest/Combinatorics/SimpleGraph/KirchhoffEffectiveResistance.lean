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

/-- The triangle has three spanning trees. -/
example :
    (∑ᶠ T : {T : (⊤ : SimpleGraph (Fin 3)).Subgraph // IsSpanningTree T},
      ∏ᶠ e ∈ T.1.edgeSet, (fun _ => (1:ℝ)) e) = 3 := by
  have hwt := weighted_matrix_tree (⊤ : SimpleGraph (Fin 3)) (fun _ => (1:ℝ)) 0
  rw [hwt, EndpointMapMultigraph.laplacian_dart_eq_lapMatrix]
  have hmap : ((⊤ : SimpleGraph (Fin 3)).lapMatrix ℤ).map (Int.castRingHom ℝ)
      = (⊤ : SimpleGraph (Fin 3)).lapMatrix ℝ := by
    ext x y
    simp only [Matrix.map_apply, SimpleGraph.lapMatrix, Matrix.sub_apply, map_sub,
      SimpleGraph.degMatrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
    split_ifs <;> simp
  have h3 : (reducedLaplacian (⊤ : SimpleGraph (Fin 3)) 0).det = 3 := by decide
  rw [reducedLaplacian_eq_lapMatrix_submatrix] at h3
  have hdet := congrArg (Int.castRingHom ℝ) h3
  rw [RingHom.map_det_submatrix, hmap] at hdet
  simpa using hdet

/-- A disconnected graph has weighted spanning-tree sum zero. -/
example :
    (∑ᶠ T : {T : (⊥ : SimpleGraph (Fin 2)).Subgraph // IsSpanningTree T},
      ∏ᶠ e ∈ T.1.edgeSet, (fun _ => (1:ℝ)) e) = 0 := by
  have hwt := weighted_matrix_tree (⊥ : SimpleGraph (Fin 2)) (fun _ => (1:ℝ)) 0
  rw [hwt, EndpointMapMultigraph.laplacian_dart_eq_lapMatrix]
  have hmap : ((⊥ : SimpleGraph (Fin 2)).lapMatrix ℤ).map (Int.castRingHom ℝ)
      = (⊥ : SimpleGraph (Fin 2)).lapMatrix ℝ := by
    ext x y
    simp only [Matrix.map_apply, SimpleGraph.lapMatrix, Matrix.sub_apply, map_sub,
      SimpleGraph.degMatrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
    split_ifs <;> simp
  have h0 : (reducedLaplacian (⊥ : SimpleGraph (Fin 2)) 0).det = 0 := by decide
  rw [reducedLaplacian_eq_lapMatrix_submatrix] at h0
  have hdet := congrArg (Int.castRingHom ℝ) h0
  rw [RingHom.map_det_submatrix, hmap] at hdet
  simp

/-- The weighted theorem applies to arbitrary conductances on the triangle. -/
example (c : Sym2 (Fin 3) → ℝ) :
    (∑ᶠ T : {T : (⊤ : SimpleGraph (Fin 3)).Subgraph // IsSpanningTree T},
      ∏ᶠ e ∈ T.1.edgeSet, c e)
      = ((EndpointMapMultigraph.laplacian (fun d : (⊤ : SimpleGraph (Fin 3)).Dart => d.fst)
          (fun d => d.snd) (fun d => c d.edge / 2)).submatrix
          (Subtype.val : {y : Fin 3 // y ≠ 0} → Fin 3)
          (Subtype.val : {y : Fin 3 // y ≠ 0} → Fin 3)).det :=
  weighted_matrix_tree (⊤ : SimpleGraph (Fin 3)) c 0

end MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted
