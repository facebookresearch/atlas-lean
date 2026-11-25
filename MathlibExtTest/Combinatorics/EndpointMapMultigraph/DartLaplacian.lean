/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.DartLaplacian

@[expose] public section

namespace EndpointMapMultigraphDartLaplacianTest

open EndpointMapMultigraph Matrix

/-- The quadratic form of `lapMatrix` is half the sum over darts of squared differences. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) = ∑ d : G.Dart, 1 / 2 * (x d.fst - x d.snd) ^ 2 := by
  rw [← laplacian_dart_eq_lapMatrix, dotProduct_mulVec_laplacian]

/-- The multigraph facts transfer: `lapMatrix` kills constants and is positive semidefinite. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.lapMatrix ℝ *ᵥ 1 = 0 ∧ (G.lapMatrix ℝ).PosSemidef := by
  rw [← laplacian_dart_eq_lapMatrix]
  exact ⟨laplacian_mulVec_one _ _ _, posSemidef_laplacian _ _ fun _ => by norm_num⟩

/-- A concrete instance: the entry of `K₂`'s multigraph Laplacian at `(0, 1)` is `-1`. -/
example : laplacian (fun d : (⊤ : SimpleGraph (Fin 2)).Dart => d.fst) (fun d => d.snd)
    (fun _ => (1 / 2 : ℝ)) 0 1 = -1 := by
  rw [laplacian_dart_eq_lapMatrix]
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix]

end EndpointMapMultigraphDartLaplacianTest
