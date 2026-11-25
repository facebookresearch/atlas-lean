/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.EffectiveResistance
public import MathlibExt.Combinatorics.SimpleGraph.MatrixTree

import MathlibExt.Combinatorics.EndpointMapMultigraph.DartLaplacian
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Kirchhoff's effective resistance formula

The fraction of spanning trees containing an edge is the effective resistance across that edge
in a finite connected simple graph with unit conductances. Grounding the Laplacian at one
endpoint turns edge deletion into a change to a single diagonal entry, so Cramer's rule
and the matrix-tree theorem give the fraction.
-/

namespace MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted

open MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
open Matrix

private theorem card_trees_delete_edge_add {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (u v : V) [DecidableRel (G.deleteEdges {s(u, v)}).Adj] :
    Nat.card {T : G.Subgraph // IsSpanningTree T ∧ T.Adj u v} +
        numSpanningTrees (G.deleteEdges {s(u, v)}) = numSpanningTrees G := by
  classical
  let S := {T : G.Subgraph // IsSpanningTree T}
  let p : S → Prop := fun T => T.1.Adj u v
  let A := {H : SimpleGraph V // H ≤ G ∧ H.IsTree}
  let H := G.deleteEdges {s(u, v)}
  have hle (K : SimpleGraph V) : K ≤ H ↔ K ≤ G ∧ ¬ K.Adj u v := by
    constructor
    · intro h
      exact ⟨h.trans (G.deleteEdges_le _), fun huv => (SimpleGraph.deleteEdges_adj.mp (h huv)).2
        (Set.mem_singleton _)⟩
    · rintro ⟨h, huv⟩ a b hab
      refine SimpleGraph.deleteEdges_adj.mpr ⟨h hab, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact huv hab
      · exact huv hab.symm
  have havoid : {T : S // ¬ p T} ≃ {K : SimpleGraph V // K ≤ H ∧ K.IsTree} := by
    refine ((spanningTreeSubgraphEquiv G).subtypeEquiv
      (q := fun K : A => ¬ K.1.Adj u v) (fun _ => Iff.rfl)).trans ?_
    refine (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun K : SimpleGraph V => K ≤ G ∧ K.IsTree) (fun K => ¬ K.Adj u v)).trans
      (Equiv.subtypeEquivRight ?_)
    intro K
    rw [hle]
    tauto
  have hin := Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (IsSpanningTree (G := G)) (fun T => T.Adj u v))
  rw [numSpanningTrees_eq_card_trees H, ← Nat.card_congr havoid, ← hin, ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl p)

private theorem det_grounded_lapMatrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ((G.lapMatrix ℝ).submatrix (Subtype.val : {x : V // x ≠ v} → V) Subtype.val).det =
      (numSpanningTrees G : ℝ) := by
  have hmap : (G.lapMatrix ℤ).map (Int.castRingHom ℝ) = G.lapMatrix ℝ := by
    ext x y
    simp only [Matrix.map_apply, SimpleGraph.lapMatrix, Matrix.sub_apply, map_sub,
      SimpleGraph.degMatrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
    split_ifs <;> simp
  have hdet := congrArg (Int.castRingHom ℝ) (kirchhoff_matrix_tree_lapMatrix G v)
  rw [RingHom.map_det_submatrix, hmap] at hdet
  simpa using hdet

private theorem grounded_lapMatrix_delete_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v)
    [DecidableRel (G.deleteEdges {s(u, v)}).Adj] :
    let A : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℝ :=
      (G.lapMatrix ℝ).submatrix Subtype.val Subtype.val
    let i : {x : V // x ≠ v} := ⟨u, huv.ne⟩
    (((G.deleteEdges {s(u, v)}).lapMatrix ℝ).submatrix
      (Subtype.val : {x : V // x ≠ v} → V) Subtype.val) =
        A.updateCol i ((fun x => A x i) - Pi.single i 1) := by
  classical
  dsimp only
  let H := G.deleteEdges {s(u, v)}
  have hadj {x y : V} (hx : x ≠ v) : H.Adj x y ↔ G.Adj x y ∧ ¬ (x = u ∧ y = v) := by
    simp [H, SimpleGraph.deleteEdges_adj, hx]
  have hdeg {x : V} (hx : x ≠ v) :
      (H.degree x : ℝ) = (G.degree x : ℝ) - if x = u then 1 else 0 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    by_cases hxu : x = u
    · subst x
      have hfin : H.neighborFinset u = (G.neighborFinset u).erase v := by
        ext y
        simp [Finset.mem_erase, SimpleGraph.mem_neighborFinset, hadj huv.ne, and_comm]
      have hmem := (G.mem_neighborFinset u v).2 huv
      rw [hfin, Finset.card_erase_of_mem hmem, Nat.cast_sub (Finset.card_pos.mpr ⟨v, hmem⟩)]
      simp
    · have hfin : H.neighborFinset x = G.neighborFinset x := by
        ext y
        simp [SimpleGraph.mem_neighborFinset, hadj hx, hxu]
      simp [hfin, hxu]
  let A : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℝ :=
    (G.lapMatrix ℝ).submatrix Subtype.val Subtype.val
  let i : {x : V // x ≠ v} := ⟨u, huv.ne⟩
  change (H.lapMatrix ℝ).submatrix Subtype.val Subtype.val =
    A.updateCol i ((fun x => A x i) - Pi.single i 1)
  ext x y
  have hxy : H.Adj x.1 y.1 ↔ G.Adj x.1 y.1 := by simp [hadj x.2, y.2]
  have hdeg' : (H.degree x.1 : ℝ) = (G.degree x.1 : ℝ) - if x = i then 1 else 0 := by
    simpa only [Subtype.ext_iff] using hdeg x.2
  have hentry : (H.lapMatrix ℝ) x.1 y.1 =
      A x y - if x = i ∧ y = i then 1 else 0 := by
    simp only [A, Matrix.submatrix_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, hxy]
    by_cases h : x = y
    · subst y
      simp only [ite_true, and_self, hdeg']
      ring
    · have hval : x.1 ≠ y.1 := fun h' => h (Subtype.ext h')
      have hne : ¬ (x = i ∧ y = i) := fun ⟨hx, hy⟩ => h (hx.trans hy.symm)
      simp [hval, hne]
  rw [Matrix.submatrix_apply, hentry]
  by_cases hy : y = i
  · subst y
    simp [Pi.single_apply]
  · simp [hy]

private theorem exists_grounded_potential {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    ∃ f : V → ℝ, f v = 0 ∧
      G.lapMatrix ℝ *ᵥ f = Pi.single u 1 - Pi.single v 1 := by
  let d : G.Dart := ⟨(u, v), huv⟩
  let a : G.Dart → V := fun d => d.fst
  let b : G.Dart → V := fun d => d.snd
  have hmem : Pi.single u 1 - Pi.single v 1 ∈ LinearMap.range (G.lapMatrix ℝ).mulVecLin := by
    rw [← EndpointMapMultigraph.laplacian_dart_eq_lapMatrix,
      EndpointMapMultigraph.range_laplacian_eq_range_orientedIncidence _ _
        (fun _ => show (0 : ℝ) < 1 / 2 by norm_num) (fun d => d.adj.ne)]
    refine ⟨Pi.single d 1, ?_⟩
    change EndpointMapMultigraph.orientedIncidence a b *ᵥ Pi.single d 1 = _
    rw [Matrix.mulVec_single_one]
    ext x
    simp [a, b, d, EndpointMapMultigraph.orientedIncidence_apply, Pi.single_apply, eq_comm]
  obtain ⟨f, hf⟩ := hmem
  refine ⟨f - f v • 1, by simp, ?_⟩
  change G.lapMatrix ℝ *ᵥ f = _ at hf
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, G.lapMatrix_mulVec_one_eq_zero ℝ, smul_zero,
    sub_zero, hf]

public section

/-- **Kirchhoff's effective resistance formula.** In a finite connected simple graph `G`, for
every edge `uv` the fraction of spanning trees of `G` that contain `uv` equals the effective
resistance between `u` and `v` with unit conductances, that is
`P[uv ∈ T] = R_eff(u, v)` for a uniform spanning tree `T` (R. Lyons and Y. Peres, *Probability on
Trees and Networks*, Cambridge University Press 2016, corrected online version of
19 August 2026, Section 4.2, Kirchhoff's Effective Resistance Formula, with `c ≡ 1`). The
effective resistance is that of the multigraph of darts of `G` with conductance `1/2` on each
dart, whose Laplacian is `SimpleGraph.lapMatrix ℝ G`
(`EndpointMapMultigraph.laplacian_dart_eq_lapMatrix`), so that each edge of `G` is one unit
resistor. -/
theorem card_spanningTree_adj_div_numSpanningTrees {V : Type*} [Fintype V]
    [DecidableEq V] (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) {u v : V}
    (huv : G.Adj u v) :
    (Nat.card {T : G.Subgraph // IsSpanningTree T ∧ T.Adj u v} : ℝ) / numSpanningTrees G =
      EndpointMapMultigraph.effectiveResistance (fun d : G.Dart => d.fst)
        (fun d : G.Dart => d.snd) (fun _ => (1 / 2 : ℝ)) u v := by
  classical
  let H := G.deleteEdges {s(u, v)}
  let : DecidableRel H.Adj := Classical.decRel _
  let A : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℝ :=
    (G.lapMatrix ℝ).submatrix Subtype.val Subtype.val
  let i : {x : V // x ≠ v} := ⟨u, huv.ne⟩
  let b : {x : V // x ≠ v} → ℝ := Pi.single i 1
  obtain ⟨f, hfv, hf⟩ := exists_grounded_potential huv
  have hr := (EndpointMapMultigraph.effectiveResistance_eq_sub_of_laplacian_mulVec
    (fun d : G.Dart => d.fst) (fun d => d.snd)
    (show 0 ≤ (fun _ : G.Dart => (1 / 2 : ℝ)) from fun _ => by norm_num) huv.ne
    (by rwa [EndpointMapMultigraph.laplacian_dart_eq_lapMatrix])).1
  rw [hfv, sub_zero] at hr
  let g : {x : V // x ≠ v} → ℝ := fun x => f x
  have hground : A *ᵥ g = b := by
    ext x
    have hx := congrFun hf x.1
    rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ v, hfv, mul_zero,
      zero_add] at hx
    simpa [A, g, b, i, Matrix.mulVec, dotProduct, Pi.single_apply, x.2, Subtype.ext_iff]
      using hx
  have hcramer : A.cramer b i = A.det * f u := by
    rw [← hground, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have hdelete : (numSpanningTrees H : ℝ) = A.det - A.cramer b i := by
    rw [← det_grounded_lapMatrix H v]
    change _ = A.det - (A.updateCol i b).det
    rw [grounded_lapMatrix_delete_edge huv]
    have hcol : (fun x => A x i) - b = (fun x => A x i) + (-1 : ℝ) • b := by
      simp [sub_eq_add_neg]
    rw [hcol, Matrix.det_updateCol_add, Matrix.updateCol_eq_self, Matrix.det_updateCol_smul]
    ring
  have hcount := card_trees_delete_edge_add (G := G) u v
  have hcountR := congrArg (Nat.cast : ℕ → ℝ) hcount
  push_cast at hcountR
  have hdet : A.det = (numSpanningTrees G : ℝ) := det_grounded_lapMatrix G v
  have hpos : 0 < numSpanningTrees G := by
    rw [numSpanningTrees_eq_card_trees]
    obtain ⟨T, hle, hT⟩ := hG.exists_isTree_le
    let : Nonempty {T : SimpleGraph V // T ≤ G ∧ T.IsTree} := ⟨⟨T, hle, hT⟩⟩
    exact Nat.card_pos
  rw [hr, div_eq_iff (by exact_mod_cast hpos.ne')]
  rw [hcramer, hdet] at hdelete
  linarith

end
end MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted
