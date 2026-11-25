/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

import Mathlib.Tactic.Ring

/-!
# Simple graphs as multigraphs: Mathlib's Laplacian

`SimpleGraph.lapMatrix ℝ G = D - A` agrees with the weighted multigraph Laplacian
`EndpointMapMultigraph.laplacian` of the darts of `G` with weight `1/2`
(`laplacian_dart_eq_lapMatrix`), so the multigraph results (quadratic form, kernel, algebraic
connectivity, Cheeger bound, effective resistance) apply to `lapMatrix` and to the
matrix-tree theorem stated with it. `laplacian_apply` gives the entries of the weighted
Laplacian in general.
-/

@[expose] public section

namespace EndpointMapMultigraph

open Matrix SimpleGraph

/-- **Entries of the weighted Laplacian.** `L u v = ∑_e w_e B u e B v e`, where `B` is the
oriented incidence matrix. -/
theorem laplacian_apply {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
    (end₁ end₂ : E → V) (w : E → ℝ) (u v : V) :
    laplacian end₁ end₂ w u v =
      ∑ e, w e * orientedIncidence end₁ end₂ u e * orientedIncidence end₁ end₂ v e := by
  simp [laplacian, Matrix.mul_apply, Matrix.diagonal, mul_comm, mul_left_comm]

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem sum_dart_fst_snd (u v : V) :
    (∑ d : G.Dart, (if d.fst = u then (1:ℝ) else 0) * (if d.snd = v then 1 else 0)) =
      if G.Adj u v then 1 else 0 := by
  simp only [ite_zero_mul_ite_zero, mul_one, Finset.sum_boole]
  split_ifs with h
  · rw [Nat.cast_eq_one, Finset.card_eq_one]
    refine ⟨⟨(u, v), h⟩, ?_⟩
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; ext <;> simp_all
    · rintro rfl; simp
  · rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro d - ⟨h1, h2⟩
    exact h (h1 ▸ h2 ▸ d.adj)

private theorem sum_dart_fst_fst (u v : V) :
    (∑ d : G.Dart, (if d.fst = u then (1:ℝ) else 0) * (if d.fst = v then 1 else 0)) =
      if u = v then (G.degree u : ℝ) else 0 := by
  simp only [ite_zero_mul_ite_zero, mul_one, Finset.sum_boole]
  split_ifs with h
  · subst h; simp [← G.dart_fst_fiber_card_eq_degree u]
  · rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro d - ⟨h1, h2⟩
    exact h (h1 ▸ h2)

private theorem sum_dart_snd_snd (u v : V) :
    (∑ d : G.Dart, (if d.snd = u then (1:ℝ) else 0) * (if d.snd = v then 1 else 0)) =
      if u = v then (G.degree u : ℝ) else 0 := by
  rw [← sum_dart_fst_fst G u v]
  exact Fintype.sum_equiv (Dart.symm_involutive (G := G)).toPerm _ _ (fun d => by simp)

/-- **Mathlib's graph Laplacian as a multigraph Laplacian.** For a finite simple graph `G`, the
weighted Laplacian of the multigraph whose edges are the darts (ordered adjacent pairs) of `G`,
each with weight `1/2`, is `SimpleGraph.lapMatrix ℝ G = D - A`; each edge of `G` appears as two
opposite darts. This identifies `L_G = ∑_{(a,b) ∈ E} (δ_a - δ_b)(δ_a - δ_b)ᵀ` with
`L_G = D_G - A_G` (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025,
equation (3.3) and the remark after it). -/
theorem laplacian_dart_eq_lapMatrix :
    laplacian (fun d : G.Dart => d.fst) (fun d => d.snd) (fun _ => (1 / 2 : ℝ)) =
      G.lapMatrix ℝ := by
  ext u v
  rw [laplacian_apply]
  simp only [orientedIncidence_apply]
  have h : ∀ d : G.Dart, 1 / 2 * ((if d.fst = u then (1:ℝ) else 0) - if d.snd = u then 1 else 0) *
      ((if d.fst = v then (1:ℝ) else 0) - if d.snd = v then 1 else 0) =
      1 / 2 * ((if d.fst = u then (1:ℝ) else 0) * (if d.fst = v then 1 else 0) -
        (if d.fst = u then (1:ℝ) else 0) * (if d.snd = v then 1 else 0) -
        (if d.fst = v then (1:ℝ) else 0) * (if d.snd = u then 1 else 0) +
        (if d.snd = u then (1:ℝ) else 0) * (if d.snd = v then 1 else 0)) := fun d => by ring
  simp_rw [h]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_dart_fst_fst, sum_dart_fst_snd, sum_dart_fst_snd, sum_dart_snd_snd]
  simp only [lapMatrix, degMatrix, Matrix.sub_apply, Matrix.diagonal_apply, adjMatrix_apply]
  by_cases huv : u = v
  · subst huv; simp; ring
  · simp only [huv, ↓reduceIte, G.adj_comm v u]
    split_ifs <;> ring

end EndpointMapMultigraph
