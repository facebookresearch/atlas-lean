/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.EffectiveResistance
public import MathlibExt.Combinatorics.SimpleGraph.KirchhoffEffectiveResistance
public import MathlibExt.Combinatorics.SimpleGraph.MatrixTree
public import Mathlib.Combinatorics.SimpleGraph.Dart

import MathlibExt.Combinatorics.EndpointMapMultigraph.DartLaplacian
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Kirchhoff's weighted effective resistance formula

For a uniformly random spanning tree `T` of a finite connected graph and an edge `e = uv`,
`P[e ∈ T] = R_eff(u, v)`, the effective resistance between the endpoints of `e` when every edge
is a unit resistor (G. Kirchhoff, 1847; R. Lyons and Y. Peres, *Probability on Trees and
Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026,
Section 4.2, Kirchhoff's Effective Resistance Formula). The source proves the weighted version,
`P[e ∈ T] = c(e) R(e⁻ ↔ e⁺)` for the spanning tree drawn with probability proportional to the
product of its conductances, with Wilson's algorithm. The imported unit-conductance case is
proved by edge deletion and Cramer's rule. This module proves the weighted formula; the
weighted matrix-tree theorem `Ξ(G) = det Δ_G^{(x)}` (Lyons and Peres, Section 4.4, the paragraph
before Exercise 4.16), of which
`MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted.kirchhoff_matrix_tree_lapMatrix` is the
unit-conductance case, is proved in the imported module.

Conductances are a function `c : Sym2 V → ℝ` on the edges of `G`; the network is the multigraph of
darts of `G` with conductance `c(d.edge) / 2` on the dart `d`, so that its Laplacian is the network
Laplacian `Δ_G` of Lyons and Peres, Exercise 2.62 (each edge appears as two opposite darts).
-/

namespace MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted

open MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

open Matrix EndpointMapMultigraph

section

variable {V : Type*} (G : SimpleGraph V)

private noncomputable abbrev treeWeight (c : Sym2 V → ℝ) (T : G.Subgraph) : ℝ :=
  ∏ᶠ e ∈ T.edgeSet, c e

private noncomputable abbrev treeSum (c : Sym2 V → ℝ) : ℝ :=
  ∑ᶠ T : {T : G.Subgraph // IsSpanningTree T}, treeWeight G c T.1

/-- Giving one edge weight zero removes exactly the trees containing it from the sum. -/
private theorem treeSum_sub_update [Finite V] [DecidableEq V] (c : Sym2 V → ℝ) (u v : V) :
    (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T ∧ T.Adj u v}, treeWeight G c T.1) =
      treeSum G c - treeSum G (Function.update c s(u, v) 0) := by
  classical
  let := Fintype.ofFinite G.Subgraph
  have sum_filter (p : G.Subgraph → Prop) (w : Sym2 V → ℝ) :
      (∑ᶠ T : {T : G.Subgraph // p T}, treeWeight G w T.1) =
        ∑ T : G.Subgraph, if p T then treeWeight G w T else 0 := by
    let := Fintype.ofFinite {T : G.Subgraph // p T}
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter,
      Finset.sum_subtype (p := p) _ (by simp) (treeWeight G w)]
  unfold treeSum
  rw [sum_filter, sum_filter, sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : IsSpanningTree T
  · simp only [hT, true_and, ite_true]
    simp only [treeWeight, finprod_mem_eq_finite_toFinset_prod _ (Set.toFinite T.edgeSet)]
    by_cases h : T.Adj u v
    · have hm : s(u, v) ∈ (Set.toFinite T.edgeSet).toFinset := by
        simpa only [Set.Finite.mem_toFinset, SimpleGraph.Subgraph.mem_edgeSet] using h
      rw [Finset.prod_update_of_mem hm]
      simp [h]
    · have hm : s(u, v) ∉ (Set.toFinite T.edgeSet).toFinset := by
        simpa only [Set.Finite.mem_toFinset, SimpleGraph.Subgraph.mem_edgeSet] using h
      rw [Finset.prod_update_of_notMem hm]
      simp [h]
  · simp [hT]

private theorem treeSum_pos [Finite V] (hG : G.Connected) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) : 0 < treeSum G c := by
  classical
  obtain ⟨H, hle, hH⟩ := hG.exists_isTree_le
  let T := (spanningTreeSubgraphEquiv G).symm ⟨H, hle, hH⟩
  let := Fintype.ofFinite {T : G.Subgraph // IsSpanningTree T}
  rw [treeSum, finsum_eq_sum_of_fintype]
  apply Finset.sum_pos _ ⟨T, Finset.mem_univ T⟩
  intro S _
  rw [treeWeight, finprod_mem_eq_finite_toFinset_prod _ (Set.toFinite S.1.edgeSet)]
  exact Finset.prod_pos fun e he => hc e (S.1.edgeSet_subset ((Set.Finite.mem_toFinset _).mp he))

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private noncomputable abbrev dartLaplacian (c : Sym2 V → ℝ) : Matrix V V ℝ :=
  laplacian (fun d : G.Dart => d.fst) (fun d => d.snd) (fun d => c d.edge / 2)

private noncomputable abbrev grounded (c : Sym2 V → ℝ) (v : V) :
    Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℝ :=
  (dartLaplacian G c).submatrix Subtype.val Subtype.val

/-- Grounding at the second endpoint turns the contribution of the two darts of an edge
into one diagonal entry at the first endpoint. -/
private theorem grounded_update_zero (c : Sym2 V → ℝ) {u v : V} (huv : G.Adj u v) :
    let A := grounded G c v
    let i : {x : V // x ≠ v} := ⟨u, huv.ne⟩
    grounded G (Function.update c s(u, v) 0) v =
      A.updateCol i ((fun x => A x i) + (-c s(u, v)) • Pi.single i 1) := by
  intro A i
  let d : G.Dart := ⟨(u, v), huv⟩
  ext x y
  have hdiff : grounded G c v x y - grounded G (Function.update c s(u, v) 0) v x y =
      if x = i ∧ y = i then c s(u, v) else 0 := by
    simp only [grounded, submatrix_apply, dartLaplacian, laplacian_apply, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_univ ({d, d.symm} : Finset G.Dart))]
    · rw [Finset.sum_pair d.symm_ne.symm]
      have hs : d.symm.edge = s(u, v) := d.edge_symm
      have hd : d.edge = s(u, v) := rfl
      have forward (z : {x : V // x ≠ v}) :
          orientedIncidence (fun t : G.Dart => t.fst) (fun t => t.snd) z.val d =
            if z = i then 1 else 0 := by
        simp [orientedIncidence_apply, d, i, Subtype.ext_iff, Ne.symm z.2, eq_comm]
      have reverse (z : {x : V // x ≠ v}) :
          orientedIncidence (fun t : G.Dart => t.fst) (fun t => t.snd) z.val d.symm =
            -(if z = i then 1 else 0) := by
        simp [orientedIncidence_apply, d, i, Subtype.ext_iff, Ne.symm z.2, eq_comm,
          SimpleGraph.Dart.symm]
      simp only [hs, hd, Function.update_self, zero_div, zero_mul, sub_zero, forward, reverse]
      split_ifs <;> simp_all
    · intro t _ ht
      have hne : t.edge ≠ d.edge := by simpa [SimpleGraph.dart_edge_eq_iff] using ht
      have hne' : t.edge ≠ s(u, v) := hne
      simp [Function.update_of_ne hne']
  by_cases hy : y = i
  · subst y
    by_cases hx : x = i <;> simp [hx, A] at hdiff ⊢ <;> linarith
  · simp [hy, A] at hdiff ⊢
    linarith

private theorem exists_weighted_grounded_potential (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) {u v : V} (huv : G.Adj u v) :
    ∃ f : V → ℝ, f v = 0 ∧ dartLaplacian G c *ᵥ f = Pi.single u 1 - Pi.single v 1 := by
  let d : G.Dart := ⟨(u, v), huv⟩
  have hmem : Pi.single u 1 - Pi.single v 1 ∈ LinearMap.range (dartLaplacian G c).mulVecLin := by
    rw [dartLaplacian, range_laplacian_eq_range_orientedIncidence (fun t : G.Dart => t.fst)
      (fun t => t.snd) (fun t => half_pos (hc t.edge t.edge_mem)) (fun t => t.adj.ne)]
    refine ⟨Pi.single d 1, ?_⟩
    change orientedIncidence _ _ *ᵥ Pi.single d 1 = _
    rw [Matrix.mulVec_single_one]
    ext x
    simp [d, orientedIncidence_apply, Pi.single_apply, eq_comm]
  obtain ⟨f, hf⟩ := hmem
  refine ⟨f - f v • 1, by simp, ?_⟩
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, dartLaplacian, laplacian_mulVec_one,
    smul_zero, sub_zero]
  exact hf

end

/-- **Kirchhoff's effective resistance formula, weighted.** In a finite connected simple graph `G`
with positive conductances `c` on its edges, let `T` be the random spanning tree drawn with
probability proportional to `Ξ(T) = ∏_{e ∈ T} c(e)`. For every edge `uv`,
`P[uv ∈ T] = c(uv) R(u ↔ v)` (R. Lyons and Y. Peres, *Probability on Trees and Networks*,
Cambridge University Press 2016, corrected online version of 19 August 2026, Section 4.2,
Kirchhoff's Effective Resistance Formula). The effective resistance is that of the dart multigraph
of `G` with conductance `c(d.edge) / 2` on the dart `d`. -/
public theorem weighted_spanningTree_adj_div {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) {u v : V} (huv : G.Adj u v) :
    (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T ∧ T.Adj u v}, ∏ᶠ e ∈ T.1.edgeSet, c e) /
        (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T}, ∏ᶠ e ∈ T.1.edgeSet, c e) =
      c s(u, v) * EndpointMapMultigraph.effectiveResistance (fun d : G.Dart => d.fst)
        (fun d : G.Dart => d.snd) (fun d => c d.edge / 2) u v := by
  let A := grounded G c v
  let i : {x : V // x ≠ v} := ⟨u, huv.ne⟩
  let b : {x : V // x ≠ v} → ℝ := Pi.single i 1
  obtain ⟨f, hfv, hf⟩ := exists_weighted_grounded_potential G c hc huv
  have hr := (effectiveResistance_eq_sub_of_laplacian_mulVec _ _
    (fun d : G.Dart => (half_pos (hc d.edge d.edge_mem)).le) huv.ne hf).1
  rw [hfv, sub_zero] at hr
  have hground : A *ᵥ (fun x => f x.val) = b := by
    ext x
    have hx := congrFun hf x.val
    rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ v, hfv, mul_zero,
      zero_add] at hx
    simpa [A, grounded, b, i, Matrix.mulVec, dotProduct, Pi.single_apply, x.2, Subtype.ext_iff]
      using hx
  have hcramer : A.cramer b i = A.det * f u := by
    rw [← hground, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have hdelete : treeSum G (Function.update c s(u, v) 0) =
      A.det + (-c s(u, v)) * A.cramer b i := by
    rw [treeSum, weighted_matrix_tree G _ v]
    change (grounded G (Function.update c s(u, v) 0) v).det = _
    rw [grounded_update_zero G c huv, Matrix.det_updateCol_add, Matrix.updateCol_eq_self,
      Matrix.det_updateCol_smul]
    rfl
  rw [treeSum_sub_update, div_eq_iff (treeSum_pos G hG c hc).ne', hr, hdelete,
    hcramer, show treeSum G c = A.det from weighted_matrix_tree G c v]
  ring

end MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted
