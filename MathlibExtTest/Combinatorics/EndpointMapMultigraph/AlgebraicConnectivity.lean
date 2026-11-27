/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.AlgebraicConnectivity

@[expose] public section

namespace EndpointMapMultigraphAlgebraicConnectivityTest

open EndpointMapMultigraph Matrix

/-- One edge joining the two vertices of `Fin 2` gives a connected underlying graph. -/
theorem edge_connected :
    (underlyingGraph (fun _ : Unit => (0 : Fin 2)) (fun _ => 1)).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ⟨0⟩⟩
  have h01 : (underlyingGraph (fun _ : Unit => (0 : Fin 2)) (fun _ => 1)).Reachable 0 1 :=
    (underlyingGraph_adj_of_ne (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (e := ())
      (by decide)).reachable
  fin_cases u <;> fin_cases v
  · rfl
  · exact h01
  · exact h01.symm
  · rfl

/-- The weighted edge has positive algebraic connectivity (Lemma 3.1.1, `⇐`). -/
example : 0 < algebraicConnectivity (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) :=
  (algebraicConnectivity_pos_iff _ _ (fun _ => by norm_num) (fun _ => by decide)
    (by simp)).2 edge_connected

/-- Two isolated vertices (no edges) have algebraic connectivity at most `0`
(Lemma 3.1.1, `⇒`). -/
example : algebraicConnectivity (fun e : Empty => e.elim) (fun e : Empty => (e.elim : Fin 2))
    (fun _ => 1) ≤ 0 := by
  by_contra h
  push Not at h
  have hc := (algebraicConnectivity_pos_iff (fun e : Empty => (e.elim : Fin 2))
    (fun e : Empty => (e.elim : Fin 2)) (w := fun _ => 1) (fun e => e.elim) (fun e => e.elim)
    (by simp)).1 h
  have hr := hc.preconnected 0 1
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  rcases Relation.ReflTransGen.cases_tail hr with h01 | ⟨c, -, hc1⟩
  · exact absurd h01 (by decide)
  · obtain ⟨-, e, -⟩ := (underlyingGraph_adj _ _).1 hc1
    exact e.elim

/-- `λ₂` of the weighted edge bounds the Rayleigh quotient of `(1, -1)`. -/
example : algebraicConnectivity (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) *
      (![1, -1] ⬝ᵥ ![1, -1]) ≤
    ![1, -1] ⬝ᵥ (laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) *ᵥ ![1, -1]) :=
  algebraicConnectivity_mul_le _ _ (fun _ => by norm_num) (by simp [dotProduct])

/-- Doubling the weight of the edge cannot lower `λ₂` (Corollary 6.2.2). -/
example : algebraicConnectivity (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) ≤
    algebraicConnectivity (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 6) :=
  algebraicConnectivity_mono _ _ fun _ => by norm_num

/-- Every Laplacian eigenvalue is monotone under a Loewner comparison. -/
example (k : Fin (Fintype.card (Fin 2))) :
    (isSymmetric_toEuclideanLin_laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1)
        (fun _ => 3)).eigenvalues finrank_euclideanSpace k ≤
      (isSymmetric_toEuclideanLin_laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1)
        (fun _ => 6)).eigenvalues finrank_euclideanSpace k :=
  eigenvalues_laplacian_le_of_posSemidef _ _
    (posSemidef_laplacian_sub_of_le _ _ fun _ => by norm_num) k

end EndpointMapMultigraphAlgebraicConnectivityTest
