/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.PlanarFaceGeometric
import Code.Lattice.JordanEnclosure
import Code.Lattice.EulerFaces2
import Code.Lattice.JordanEulerInduction
import Code.Lattice.WhitneyBridge
import Code.Lattice.JordanEvenClose
import Code.Lattice.JordanEvenBiconditional
import Code.Lattice.JordanFaithfulCount
import Code.Lattice.JordanVeblenStep

open SimpleGraph Set

namespace StatMech

namespace Lattice










theorem jic_edge_at_q_not_mem (G : SimpleGraph (Site 2)) {q : Site 2}
    (hfree : ∀ w, ¬ G.Adj q w) {u v : Site 2} (hq : u = q ∨ v = q) :
    s(u, v) ∉ G.edgeSet := by
  rw [SimpleGraph.mem_edgeSet]
  intro hG
  rcases hq with rfl | rfl
  · exact hfree v hG
  · exact hfree u hG.symm


theorem jic_adj_NE_NW (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a - 1, b] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

theorem jic_adj_NW_SW (a b : ℤ) : (hypercubicLattice 2).Adj ![a - 1, b] ![a - 1, b - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

theorem jic_adj_SW_SE (a b : ℤ) : (hypercubicLattice 2).Adj ![a - 1, b - 1] ![a, b - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

theorem jic_adj_SE_NE (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b - 1] ![a, b] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp


theorem jic_shared_NE_NW (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a - 1, b] = s(![a, b], ![a, b + 1]) := by
  rw [sharedPrimalEdge_left]; unfold faceCorner00 faceCorner01; rfl

theorem jic_shared_NW_SW (a b : ℤ) :
    sharedPrimalEdge ![a - 1, b] ![a - 1, b - 1] = s(![a - 1, b], ![a, b]) := by
  unfold sharedPrimalEdge
  rw [if_pos (by simp only [Matrix.cons_val_zero])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max b (b - 1) = b by omega]
  rw [Sym2.eq_iff]; left; constructor <;> (funext i; fin_cases i <;> simp <;> try omega)

theorem jic_shared_SW_SE (a b : ℤ) :
    sharedPrimalEdge ![a - 1, b - 1] ![a, b - 1] = s(![a, b - 1], ![a, b]) := by
  unfold sharedPrimalEdge
  rw [if_neg (by simp only [Matrix.cons_val_zero]; omega)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max (a - 1) a = a by omega]
  rw [Sym2.eq_iff]; left; constructor <;> (funext i; fin_cases i <;> simp <;> try omega)

theorem jic_shared_SE_NE (a b : ℤ) :
    sharedPrimalEdge ![a, b - 1] ![a, b] = s(![a, b], ![a + 1, b]) := by
  unfold sharedPrimalEdge
  rw [if_pos (by simp only [Matrix.cons_val_zero])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max (b - 1) b = b by omega]


theorem jic_faces_distinct (a b : ℤ) :
    (![a, b] : Site 2) ≠ ![a - 1, b] ∧ (![a, b] : Site 2) ≠ ![a - 1, b - 1] ∧
      (![a, b] : Site 2) ≠ ![a, b - 1] ∧ (![a - 1, b] : Site 2) ≠ ![a - 1, b - 1] ∧
      (![a - 1, b] : Site 2) ≠ ![a, b - 1] ∧ (![a - 1, b - 1] : Site 2) ≠ ![a, b - 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have h0 := congrFun h 0; have h1 := congrFun h 1;
     simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1; omega)








theorem jic_pres_NE_NW (G : SimpleGraph (Site 2)) (a b : ℤ)
    (hfree : ∀ w, ¬ G.Adj ![a, b] w) : (whb_faceRegion G).Adj ![a, b] ![a - 1, b] := by
  refine ⟨jic_adj_NE_NW a b, ?_⟩
  rw [jic_shared_NE_NW]; exact jic_edge_at_q_not_mem G hfree (Or.inl rfl)

theorem jic_pres_NW_SW (G : SimpleGraph (Site 2)) (a b : ℤ)
    (hfree : ∀ w, ¬ G.Adj ![a, b] w) : (whb_faceRegion G).Adj ![a - 1, b] ![a - 1, b - 1] := by
  refine ⟨jic_adj_NW_SW a b, ?_⟩
  rw [jic_shared_NW_SW]; exact jic_edge_at_q_not_mem G hfree (Or.inr rfl)

theorem jic_pres_SW_SE (G : SimpleGraph (Site 2)) (a b : ℤ)
    (hfree : ∀ w, ¬ G.Adj ![a, b] w) : (whb_faceRegion G).Adj ![a - 1, b - 1] ![a, b - 1] := by
  refine ⟨jic_adj_SW_SE a b, ?_⟩
  rw [jic_shared_SW_SE]; exact jic_edge_at_q_not_mem G hfree (Or.inr rfl)

theorem jic_pres_SE_NE (G : SimpleGraph (Site 2)) (a b : ℤ)
    (hfree : ∀ w, ¬ G.Adj ![a, b] w) : (whb_faceRegion G).Adj ![a, b - 1] ![a, b] := by
  refine ⟨jic_adj_SE_NE a b, ?_⟩
  rw [jic_shared_SE_NE]; exact jic_edge_at_q_not_mem G hfree (Or.inl rfl)













theorem jic_surv_reachable (G : SimpleGraph (Site 2)) (e : Sym2 (Site 2)) {u v : Site 2}
    (hadj : (whb_faceRegion G).Adj u v) (hne : s(u, v) ≠ e) :
    ((whb_faceRegion G).deleteEdges {e}).Reachable u v :=
  (SimpleGraph.deleteEdges_adj.mpr ⟨hadj, by rw [Set.mem_singleton_iff]; exact hne⟩).reachable




theorem jic_quad_edge_ne {u₁ v₁ u₂ v₂ : Site 2}
    (h : ¬ ((u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂))) : s(u₁, v₁) ≠ s(u₂, v₂) := by
  rw [ne_eq, Sym2.eq_iff]; exact h



theorem jic_dangling_east (G : SimpleGraph (Site 2)) (a b : ℤ) (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
    ((whb_faceRegion G).deleteEdges {s((![a, b] : Site 2), ![a, b - 1])}).Reachable
      ![a, b] ![a, b - 1] := by
  have ne1 : s((![a, b] : Site 2), ![a - 1, b]) ≠ s((![a, b] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne2 : s((![a - 1, b] : Site 2), ![a - 1, b - 1]) ≠ s((![a, b] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne3 : s((![a - 1, b - 1] : Site 2), ![a, b - 1]) ≠ s((![a, b] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have r1 := jic_surv_reachable G _ (jic_pres_NE_NW G a b hfree) ne1
  have r2 := jic_surv_reachable G _ (jic_pres_NW_SW G a b hfree) ne2
  have r3 := jic_surv_reachable G _ (jic_pres_SW_SE G a b hfree) ne3
  exact (r1.trans r2).trans r3



theorem jic_dangling_north (G : SimpleGraph (Site 2)) (a b : ℤ) (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
    ((whb_faceRegion G).deleteEdges {s((![a, b] : Site 2), ![a - 1, b])}).Reachable
      ![a, b] ![a - 1, b] := by
  have ne1 : s((![a, b - 1] : Site 2), ![a, b]) ≠ s((![a, b] : Site 2), ![a - 1, b]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne2 : s((![a - 1, b - 1] : Site 2), ![a, b - 1]) ≠ s((![a, b] : Site 2), ![a - 1, b]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne3 : s((![a - 1, b] : Site 2), ![a - 1, b - 1]) ≠ s((![a, b] : Site 2), ![a - 1, b]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have r1 := jic_surv_reachable G _ (jic_pres_SE_NE G a b hfree) ne1
  have r2 := jic_surv_reachable G _ (jic_pres_SW_SE G a b hfree) ne2
  have r3 := jic_surv_reachable G _ (jic_pres_NW_SW G a b hfree) ne3
  
  exact ((r1.symm.trans r2.symm).trans r3.symm)



theorem jic_dangling_west (G : SimpleGraph (Site 2)) (a b : ℤ) (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
    ((whb_faceRegion G).deleteEdges {s((![a - 1, b] : Site 2), ![a - 1, b - 1])}).Reachable
      ![a - 1, b] ![a - 1, b - 1] := by
  have ne1 : s((![a, b] : Site 2), ![a - 1, b]) ≠ s((![a - 1, b] : Site 2), ![a - 1, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne2 : s((![a, b - 1] : Site 2), ![a, b]) ≠ s((![a - 1, b] : Site 2), ![a - 1, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne3 : s((![a - 1, b - 1] : Site 2), ![a, b - 1]) ≠ s((![a - 1, b] : Site 2), ![a - 1, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have r1 := jic_surv_reachable G _ (jic_pres_NE_NW G a b hfree) ne1
  have r2 := jic_surv_reachable G _ (jic_pres_SE_NE G a b hfree) ne2
  have r3 := jic_surv_reachable G _ (jic_pres_SW_SE G a b hfree) ne3
  
  exact ((r1.symm.trans r2.symm).trans r3.symm)



theorem jic_dangling_south (G : SimpleGraph (Site 2)) (a b : ℤ) (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
    ((whb_faceRegion G).deleteEdges {s((![a - 1, b - 1] : Site 2), ![a, b - 1])}).Reachable
      ![a - 1, b - 1] ![a, b - 1] := by
  have ne1 : s((![a - 1, b] : Site 2), ![a - 1, b - 1]) ≠ s((![a - 1, b - 1] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne2 : s((![a, b] : Site 2), ![a - 1, b]) ≠ s((![a - 1, b - 1] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne3 : s((![a, b - 1] : Site 2), ![a, b]) ≠ s((![a - 1, b - 1] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have r1 := jic_surv_reachable G _ (jic_pres_NW_SW G a b hfree) ne1
  have r2 := jic_surv_reachable G _ (jic_pres_NE_NW G a b hfree) ne2
  have r3 := jic_surv_reachable G _ (jic_pres_SE_NE G a b hfree) ne3
  
  exact ((r1.symm.trans r2.symm).trans r3.symm)











theorem jic_dangling_bridge (G : SimpleGraph (Site 2)) {p q : Site 2}
    (hfree : ∀ w, ¬ G.Adj q w) (hpq : (hypercubicLattice 2).Adj p q) :
    ∃ f0 g0 : Site 2, (hypercubicLattice 2).Adj f0 g0 ∧
      sharedPrimalEdge f0 g0 = s(p, q) ∧
      ((whb_faceRegion G).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  obtain ⟨a, b, hqf⟩ : ∃ a b : ℤ, q = ![a, b] := ⟨q 0, q 1, by funext i; fin_cases i <;> rfl⟩
  subst hqf
  have hpq' := hpq
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpq'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hpq'
  have hcase : (p = ![a + 1, b]) ∨ (p = ![a - 1, b]) ∨ (p = ![a, b + 1]) ∨ (p = ![a, b - 1]) := by
    have hh : (p 0 = a ∧ (p 1 = b + 1 ∨ p 1 = b - 1)) ∨
        (p 1 = b ∧ (p 0 = a + 1 ∨ p 0 = a - 1)) := by omega
    rcases hh with ⟨h0, (h1 | h1)⟩ | ⟨h1, (h0 | h0)⟩
    · exact Or.inr (Or.inr (Or.inl (by rw [jeb_site_eq_iff]; omega)))
    · exact Or.inr (Or.inr (Or.inr (by rw [jeb_site_eq_iff]; omega)))
    · exact Or.inl (by rw [jeb_site_eq_iff]; omega)
    · exact Or.inr (Or.inl (by rw [jeb_site_eq_iff]; omega))
  rcases hcase with rfl | rfl | rfl | rfl
  · 
    refine ⟨![a, b], ![a, b - 1], (jic_adj_SE_NE a b).symm, ?_, jic_dangling_east G a b hfree⟩
    rw [sharedPrimalEdge_comm_of_adj (jic_adj_SE_NE a b).symm, jic_shared_SE_NE, Sym2.eq_swap]
  · 
    refine ⟨![a - 1, b], ![a - 1, b - 1], jic_adj_NW_SW a b, ?_, jic_dangling_west G a b hfree⟩
    rw [jic_shared_NW_SW]
  · 
    refine ⟨![a, b], ![a - 1, b], jic_adj_NE_NW a b, ?_, jic_dangling_north G a b hfree⟩
    rw [jic_shared_NE_NW, Sym2.eq_swap]
  · 
    refine ⟨![a - 1, b - 1], ![a, b - 1], jic_adj_SW_SE a b, ?_, jic_dangling_south G a b hfree⟩
    rw [jic_shared_SW_SE, Sym2.eq_swap]











theorem jic_pushGraph_sup (P : PlanarZ2Subgraph) (A B : SimpleGraph P.V) :
    jei_pushGraph P (A ⊔ B) = jei_pushGraph P A ⊔ jei_pushGraph P B := by
  ext a b
  simp only [jei_pushGraph_adj, sup_adj]
  constructor
  · rintro ⟨x, y, (h | h), hx, hy⟩
    · exact Or.inl ⟨x, y, h, hx, hy⟩
    · exact Or.inr ⟨x, y, h, hx, hy⟩
  · rintro (⟨x, y, h, hx, hy⟩ | ⟨x, y, h, hx, hy⟩)
    · exact ⟨x, y, Or.inl h, hx, hy⟩
    · exact ⟨x, y, Or.inr h, hx, hy⟩



noncomputable def jic_tc (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) : ℕ :=
  Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent




theorem jic_emb_free_of_isolated (P : PlanarZ2Subgraph) (H : SimpleGraph P.V) {x : P.V}
    (hiso : ∀ w, ¬ H.Adj x w) : ∀ w, ¬ (jei_pushGraph P H).Adj (P.emb x) w := by
  rintro w ⟨u, v, huv, hu, hv⟩
  have : u = x := P.emb.injective hu
  subst this
  exact hiso v huv





theorem jic_tc_sup_edge_keep (P : PlanarZ2Subgraph) (H : SimpleGraph P.V) {x z : P.V}
    (hxz : x ≠ z) (hadjG : (hypercubicLattice 2).Adj (P.emb x) (P.emb z))
    (hiso : ∀ w, ¬ H.Adj x w) :
    jic_tc P (H ⊔ edge x z) = jic_tc P H := by
  classical
  haveI hfinH : Finite (whb_faceRegion (jei_pushGraph P H)).ConnectedComponent :=
    jfc_whb_pushGraph_regionComponents_finite P H
  haveI hfinHe : Finite (whb_faceRegion (jei_pushGraph P (H ⊔ edge x z))).ConnectedComponent :=
    jfc_whb_pushGraph_regionComponents_finite P (H ⊔ edge x z)
  set p := P.emb x with hp
  set q := P.emb z with hq
  have hpq : p ≠ q := fun h => hxz (P.emb.injective h)
  have hpushEq : jei_pushGraph P (H ⊔ edge x z) = jei_pushGraph P H ⊔ edge p q := by
    rw [jei_pushGraph_sup_edge P H x z hxz]
  
  have hfree : ∀ w, ¬ (jei_pushGraph P H).Adj p w := jic_emb_free_of_isolated P H hiso
  
  obtain ⟨f0, g0, hfg, hshared, hreach⟩ :=
    jic_dangling_bridge (jei_pushGraph P H) hfree hadjG.symm
  
  
  have hnotmem : sharedPrimalEdge f0 g0 ∉ (jei_pushGraph P H).edgeSet := by
    rw [hshared, SimpleGraph.mem_edgeSet]
    intro hh; exact hfree q hh.symm
  have hpres : s(f0, g0) ∈ (whb_faceRegion (jei_pushGraph P H)).edgeSet := by
    rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]; exact ⟨hfg, hnotmem⟩
  
  haveI hfinSup : Finite (whb_faceRegion (jei_pushGraph P H ⊔ edge q p)).ConnectedComponent := by
    have : jei_pushGraph P H ⊔ edge q p = jei_pushGraph P (H ⊔ edge x z) := by
      rw [hpushEq, edge_comm]
    rw [this]; exact hfinHe
  
  have hdich := jfc_whb_delete_dichotomy (jei_pushGraph P H) (p := q) (q := p)
    (f0 := f0) (g0 := g0) (Ne.symm hpq) hfg hshared hpres
  
  have hkeep := hdich.1 hreach
  
  have hswap : (jei_pushGraph P H ⊔ edge q p) = jei_pushGraph P H ⊔ edge p q := by
    rw [edge_comm]
  unfold jic_tc
  rw [hpushEq, ← hswap, hkeep]







theorem jic_addWalk_tc (P : PlanarZ2Subgraph) :
    ∀ {x y : P.V} (q : P.G.Walk x y) (H : SimpleGraph P.V), q.IsPath →
      (∀ u ∈ q.support, ∀ w, ¬ H.Adj u w) →
      jic_tc P (H ⊔ q.toSubgraph.spanningCoe) = jic_tc P H := by
  intro x y q
  induction q with
  | nil =>
    intro H _ _
    congr 1
    exact jvp_sup_nil_spanningCoe x H
  | @cons x z y hadj p ih =>
    intro H hpath hiso
    obtain ⟨hpp, hxns⟩ := (Walk.cons_isPath_iff hadj p).mp hpath
    have hiso_p : ∀ u ∈ p.support, ∀ w, ¬ H.Adj u w := fun u hu w =>
      hiso u (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hu) w
    
    set Hp := H ⊔ p.toSubgraph.spanningCoe with hHp
    have ihHp : jic_tc P Hp = jic_tc P H := ih H hpp hiso_p
    
    have hxinsupp : x ∈ (Walk.cons hadj p).support := by
      rw [Walk.support_cons]; exact List.mem_cons_self
    have hxiso : ∀ w, ¬ Hp.Adj x w := by
      intro w hadjw
      rw [hHp, sup_adj] at hadjw
      rcases hadjw with h | h
      · exact hiso x hxinsupp w h
      · rw [Subgraph.spanningCoe_adj] at h
        exact hxns (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert h))
    have hxz : x ≠ z := fun h => hxns (h ▸ Walk.start_mem_support p)
    
    have hunion : H ⊔ (Walk.cons hadj p).toSubgraph.spanningCoe = Hp ⊔ edge x z := by
      rw [jvp_consSpanningCoe hadj p, hHp]; ac_rfl
    
    have hlat : (hypercubicLattice 2).Adj (P.emb x) (P.emb z) := P.isSub hadj
    
    have hkeep := jic_tc_sup_edge_keep P Hp hxz hlat hxiso
    rw [hunion, hkeep, ihHp]





theorem jic_isCycles_closedContour (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    [DecidableRel K.Adj] (hKle : K ≤ P.G) (hcyc : K.IsCycles) :
    jce_ClosedContour (jei_pushGraph P K).edgeSet := by
  classical
  haveI : Fintype P.V := Fintype.ofFinite _
  haveI hlf : SimpleGraph.LocallyFinite (jei_pushGraph P K) := jfc_pushGraph_locallyFinite P K hKle
  haveI hlfK : SimpleGraph.LocallyFinite K := fun v => Fintype.ofFinite _
  have hsub : jei_pushGraph P K ≤ hypercubicLattice 2 := jfc_pushGraph_le_lattice P K hKle
  intro s
  rw [jeb_jce_degree_eq_degree (jei_pushGraph P K) hsub s]
  
  by_cases hs : ∃ v : P.V, P.emb v = s
  · obtain ⟨v, rfl⟩ := hs
    have hdeg : (jei_pushGraph P K).degree (P.emb v) = K.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
      symm
      apply Finset.card_bij (fun w _ => P.emb w)
      · intro w hw
        rw [SimpleGraph.mem_neighborFinset] at hw
        rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj]
        exact ⟨v, w, hw, rfl, rfl⟩
      · intro a _ b _ h; exact P.emb.injective h
      · intro w hw
        rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj] at hw
        obtain ⟨x, y, hxy, hx, hy⟩ := hw
        have hxv : x = v := P.emb.injective hx
        subst hxv
        exact ⟨y, by rw [SimpleGraph.mem_neighborFinset]; exact hxy, hy⟩
    rw [hdeg]
    have h := jvp_isCycles_even hcyc v
    rwa [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at h
  · 
    have hzero : (jei_pushGraph P K).degree s = 0 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj] at hw
      obtain ⟨x, y, _, hx, _⟩ := hw
      exact hs ⟨x, hx⟩
    rw [hzero]; exact ⟨0, rfl⟩















theorem jic_tc_close_edge (P : PlanarZ2Subgraph) (Kq : SimpleGraph P.V) [DecidableRel Kq.Adj]
    (hKqle : Kq ≤ P.G) {v z : P.V} (hadjG : P.G.Adj v z) (hnotKq : ¬ Kq.Adj v z)
    (hreach : Kq.Reachable v z)
    (hccK : jce_ClosedContour (jei_pushGraph P (Kq ⊔ edge v z)).edgeSet) :
    jic_tc P (Kq ⊔ edge v z) = jic_tc P Kq + 1 := by
  classical
  haveI hfinKq : Finite (whb_faceRegion (jei_pushGraph P Kq)).ConnectedComponent :=
    jfc_whb_pushGraph_regionComponents_finite P Kq
  haveI hfinK : Finite (whb_faceRegion (jei_pushGraph P (Kq ⊔ edge v z))).ConnectedComponent :=
    jfc_whb_pushGraph_regionComponents_finite P (Kq ⊔ edge v z)
  have hvz : v ≠ z := hadjG.ne
  set p := P.emb v with hp
  set q := P.emb z with hq
  have hpq : p ≠ q := fun h => hvz (P.emb.injective h)
  have hlatpq : (hypercubicLattice 2).Adj p q := P.isSub hadjG
  
  obtain ⟨f0, g0, hfg, hshared⟩ := jfc_flankingFaces hlatpq
  have hpres : s(f0, g0) ∈ (whb_faceRegion (jei_pushGraph P Kq)).edgeSet :=
    jfc_flankingEdge_present P Kq hadjG hnotKq hfg hshared
  
  
  have hcontourEq : ((insert (sharedPrimalEdge f0 g0)
        (jei_pushGraph_edgeSet_finite P Kq).toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))
      = (jei_pushGraph P (Kq ⊔ edge v z)).edgeSet := by
    rw [Finset.coe_insert, Set.Finite.coe_toFinset, hshared,
      jei_pushGraph_sup_edge P Kq v z hvz, SimpleGraph.edgeSet_sup]
    ext e
    refine e.ind (fun a c => ?_)
    simp only [Set.mem_insert_iff, Set.mem_union, SimpleGraph.mem_edgeSet, SimpleGraph.edge_adj]
    constructor
    · rintro (h | h)
      · right; rw [Sym2.eq_iff] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Or.inl ⟨rfl, rfl⟩, hpq⟩
        · exact ⟨Or.inr ⟨rfl, rfl⟩, Ne.symm hpq⟩
      · exact Or.inl h
    · rintro (h | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩)
      · exact Or.inr h
      · left; rfl
      · left; rw [Sym2.eq_swap]
  have hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) (jei_pushGraph_edgeSet_finite P Kq).toFinset
        : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
    rw [hcontourEq]; exact hccK
  have hsync := jfc_whbSync_step_of_evenContour P Kq hKqle hadjG hnotKq hfg hshared hcc
  
  have hsep : ¬ ((whb_faceRegion (jei_pushGraph P Kq)).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
    hsync.mp hreach
  
  have hpushEq : jei_pushGraph P (Kq ⊔ edge v z) = jei_pushGraph P Kq ⊔ edge p q := by
    rw [jei_pushGraph_sup_edge P Kq v z hvz]
  haveI hfinSup : Finite (whb_faceRegion (jei_pushGraph P Kq ⊔ edge p q)).ConnectedComponent := by
    rw [← hpushEq]; exact hfinK
  have hdich := jfc_whb_delete_dichotomy (jei_pushGraph P Kq) (p := p) (q := q)
    (f0 := f0) (g0 := g0) hpq hfg hshared hpres
  have hmerge := hdich.2 hsep
  unfold jic_tc
  rw [hpushEq]; omega





theorem jic_tc_deleteCycle (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) [DecidableRel K.Adj]
    (hKle : K ≤ P.G) (hcyc : K.IsCycles) {v : P.V} (p : K.Walk v v) (hp : p.IsCycle) :
    jic_tc P K = jic_tc P (K.deleteEdges p.toSubgraph.edgeSet) + 1 := by
  classical
  haveI : Finite P.V := P.finV
  haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
  
  obtain ⟨z, hadj, q, hpeq, hqpath⟩ : ∃ (z : P.V) (hadj : K.Adj v z) (q : K.Walk z v),
      p = Walk.cons hadj q ∧ q.IsPath := by
    cases p with
    | nil => exact absurd Walk.nil_nil hp.not_nil
    | cons hadj q => rw [Walk.cons_isCycle_iff] at hp; exact ⟨_, hadj, q, rfl, hp.1⟩
  set K'' := K.deleteEdges p.toSubgraph.edgeSet with hK''
  
  have hisoAll : ∀ u ∈ p.support, ∀ w, ¬ K''.Adj u w := by
    intro u hu w hadjw
    rw [hK'', deleteEdges_adj] at hadjw
    obtain ⟨hKadj, hnotin⟩ := hadjw
    have huv : u ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hu
    have := (hp.adj_toSubgraph_iff_of_isCycles hcyc huv w).mpr hKadj
    exact hnotin (by rw [Subgraph.mem_edgeSet]; exact this)
  have hqsub : ∀ u ∈ q.support, u ∈ p.support := by
    intro u hu; rw [hpeq, Walk.support_cons]; exact List.mem_cons_of_mem _ hu
  have hisoQ : ∀ u ∈ q.support, ∀ w, ¬ K''.Adj u w := fun u hu w => hisoAll u (hqsub u hu) w
  
  set qG : P.G.Walk z v := q.mapLe hKle with hqG
  
  have hqGpath : qG.IsPath := (SimpleGraph.Walk.mapLe_isPath hKle).mpr hqpath
  
  have hsupp : qG.support = q.support := by
    rw [hqG]; exact SimpleGraph.Walk.support_mapLe_eq_support hKle q
  
  have hspan : qG.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe := by
    ext w x
    rw [hqG, Subgraph.spanningCoe_adj, Subgraph.spanningCoe_adj,
      SimpleGraph.Walk.adj_toSubgraph_mapLe]
  
  have hisoQG : ∀ u ∈ qG.support, ∀ w, ¬ K''.Adj u w := by
    intro u hu w; rw [hsupp] at hu; exact hisoQ u hu w
  
  have haddK'' : K'' ≤ P.G := (deleteEdges_le _).trans hKle
  have haddwalk := jic_addWalk_tc P qG K'' hqGpath hisoQG
  
  set Kq := K'' ⊔ qG.toSubgraph.spanningCoe with hKqdef
  
  have hpspan : p.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe ⊔ edge v z := by
    rw [hpeq]; exact jvp_consSpanningCoe hadj q
  have hKeq : K = K'' ⊔ p.toSubgraph.spanningCoe := by
    ext a c
    simp only [hK'', sup_adj, deleteEdges_adj, Subgraph.spanningCoe_adj]
    constructor
    · intro hKac
      by_cases hin : s(a, c) ∈ p.toSubgraph.edgeSet
      · right; rw [Subgraph.mem_edgeSet] at hin; exact hin
      · left; exact ⟨hKac, hin⟩
    · rintro (⟨hh, _⟩ | hh)
      · exact hh
      · exact p.toSubgraph.adj_sub hh
  have hKeq2 : K = Kq ⊔ edge v z := by
    rw [hKeq, hpspan, hKqdef, hspan]; ac_rfl
  
  
  have hqreach : Kq.Reachable z v := by
    obtain ⟨_, hreachAll⟩ := jvp_addWalk_faceCount qG K'' hqGpath hisoQG
    exact hreachAll v (Walk.end_mem_support qG)
  
  have hqspanle : q.toSubgraph.spanningCoe ≤ K := by
    intro a c h; exact q.toSubgraph.adj_sub (by rwa [Subgraph.spanningCoe_adj] at h)
  have hKqle : Kq ≤ P.G := by
    rw [hKqdef]
    exact sup_le haddK'' (by rw [hspan]; exact hqspanle.trans hKle)
  
  
  have hnotKq : ¬ Kq.Adj v z := by
    rw [hKqdef, sup_adj]
    rintro (h | h)
    · exact hisoAll v (by rw [hpeq, Walk.support_cons]; exact List.mem_cons_self) z h
    · rw [hspan, Subgraph.spanningCoe_adj, q.adj_toSubgraph_iff_mem_edges] at h
      have hpc : p.IsCycle := hp
      rw [hpeq, Walk.cons_isCycle_iff] at hpc
      exact hpc.2 (by rw [Sym2.eq_swap] at h ⊢; exact h)
  have hadjG : P.G.Adj v z := hKle hadj
  
  have hccK : jce_ClosedContour (jei_pushGraph P (Kq ⊔ edge v z)).edgeSet := by
    rw [← hKeq2]; exact jic_isCycles_closedContour P K hKle hcyc
  
  haveI : DecidableRel Kq.Adj := Classical.decRel _
  have hclose := jic_tc_close_edge P Kq hKqle hadjG hnotKq hqreach.symm hccK
  
  rw [hKeq2, hclose, hKqdef, haddwalk]












theorem jic_tc_eq_faceCount (P : PlanarZ2Subgraph) :
    ∀ (K : SimpleGraph P.V), K ≤ P.G → K.IsCycles → jic_tc P K = faceCount K := by
  classical
  haveI : Finite P.V := P.finV
  haveI : DecidableEq P.V := P.decV
  intro K
  generalize hn : K.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    intro hKle hcyc
    haveI hdec : DecidableRel K.Adj := Classical.decRel _
    haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · 
      subst hz
      have hempty : K.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite K.edgeSet)).mp hn
      have hbot : K = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot
      
      unfold jic_tc
      rw [jei_pushGraph_bot, jfc_whb_bot]
      have hlat : Nat.card (hypercubicLattice 2).ConnectedComponent = 1 := by
        have hreach : ∀ a b : Site 2, (hypercubicLattice 2).Reachable a b :=
          fun a b => pbs_reach_all a b
        have hsub : Subsingleton (hypercubicLattice 2).ConnectedComponent :=
          ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hreach a b))⟩
        haveI : Nonempty (hypercubicLattice 2).ConnectedComponent :=
          ⟨(hypercubicLattice 2).connectedComponentMk ![0, 0]⟩
        rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, inferInstance⟩
      rw [hlat]
      unfold faceCount nullity
      rw [SimpleGraph.edgeSet_bot, Set.ncard_empty, card_components_bot]; simp
    · 
      have hne : K.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hne
      obtain ⟨a, b⟩ := e
      rw [SimpleGraph.mem_edgeSet] at he
      have hnbr : (K.neighborSet a).Nonempty := ⟨b, he⟩
      obtain ⟨p, hpc, _⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
        (v := a) (c := K.connectedComponentMk a) rfl hnbr
      set K' := K.deleteEdges p.toSubgraph.edgeSet with hK'
      have hK'le : K' ≤ P.G := (deleteEdges_le _).trans hKle
      have hK'cyc : K'.IsCycles := jvp_isCycles_deleteCycle_isCycles hcyc p hpc
      have hlt : K'.edgeSet.ncard < K.edgeSet.ncard := jvp_ncard_deleteCycle_lt p hpc
      have hn' : K'.edgeSet.ncard = K'.edgeSet.ncard := rfl
      
      have ihK' : jic_tc P K' = faceCount K' :=
        ih K'.edgeSet.ncard (by omega) K' rfl hK'le hK'cyc
      
      have hface := jvp_faceCount_deleteCycle K hcyc p hpc
      have hreg := jic_tc_deleteCycle P K hKle hcyc p hpc
      
      rw [hreg, ihK']
      omega



theorem jic_total_count (P : PlanarZ2Subgraph) (hcyc : P.G.IsCycles) :
    Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
  have h := jic_tc_eq_faceCount P P.G le_rfl hcyc
  unfold jic_tc at h
  rwa [jei_pushGraph_G P] at h



theorem jic_faithfulRegionCount_eq_nullity (P : PlanarZ2Subgraph) (hcyc : P.G.IsCycles) :
    whc_faithfulRegionCount P = nullity P.G := by
  have htot := jic_total_count P hcyc
  have hcard := jfc_whb_bounded_add_one_eq_card P
  rw [htot, faceCount] at hcard
  omega









theorem jic_faithfulDiscreteJordan (P : PlanarZ2Subgraph) (hcyc : P.G.IsCycles) :
    whc_FaithfulDiscreteJordan P := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)
  have heq : whc_faithfulRegionCount P = nullity P.G :=
    jic_faithfulRegionCount_eq_nullity P hcyc
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩










theorem jic_cyc4_isCycles : jbc_cyc4.IsCycles := by
  intro v _
  rw [Set.ncard_eq_two]
  fin_cases v
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jbc_cyc4Rel] <;> decide⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jbc_cyc4Rel] <;> decide⟩
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jbc_cyc4Rel] <;> decide⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jbc_cyc4Rel] <;> decide⟩



theorem jic_faithfulDiscreteJordan_unitSquare : whc_FaithfulDiscreteJordan jbc_Pce :=
  jic_faithfulDiscreteJordan jbc_Pce jic_cyc4_isCycles




theorem jic_unitSquare_count : whc_faithfulRegionCount jbc_Pce = 1 := by
  rw [jic_faithfulRegionCount_eq_nullity jbc_Pce jic_cyc4_isCycles]
  have h : faceCount jbc_Pce.G = 2 := whb_square_faceCount
  rw [faceCount] at h; omega





def jic_twoSq_emb (i : Fin 8) : Site 2 :=
  match i with
  | 0 => ![0, 0] | 1 => ![1, 0] | 2 => ![1, 1] | 3 => ![0, 1]
  | 4 => ![10, 0] | 5 => ![11, 0] | 6 => ![11, 1] | 7 => ![10, 1]

theorem jic_twoSq_emb_inj : Function.Injective jic_twoSq_emb := by decide +kernel


def jic_twoSq_rel (i j : Fin 8) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 0) || (i == 1 && j == 2) || (i == 2 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 0) || (i == 0 && j == 3) ||
  (i == 4 && j == 5) || (i == 5 && j == 4) || (i == 5 && j == 6) || (i == 6 && j == 5) ||
  (i == 6 && j == 7) || (i == 7 && j == 6) || (i == 7 && j == 4) || (i == 4 && j == 7)


def jic_twoSq_G : SimpleGraph (Fin 8) where
  Adj i j := jic_twoSq_rel i j
  symm := by intro i j h; revert h; revert i j; decide
  loopless := ⟨by intro i h; revert h; revert i; decide⟩

@[simp] theorem jic_twoSq_G_adj (i j : Fin 8) : jic_twoSq_G.Adj i j ↔ jic_twoSq_rel i j := Iff.rfl

theorem jic_twoSq_isSub : ∀ ⦃i j : Fin 8⦄, jic_twoSq_G.Adj i j →
    (hypercubicLattice 2).Adj (jic_twoSq_emb i) (jic_twoSq_emb j) := by
  intro i j h
  rw [jic_twoSq_G_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jic_twoSq_rel, jic_twoSq_emb]


noncomputable def jic_twoSq_P : PlanarZ2Subgraph where
  V := Fin 8
  finV := inferInstance
  decV := inferInstance
  G := jic_twoSq_G
  emb := ⟨jic_twoSq_emb, jic_twoSq_emb_inj⟩
  isSub := jic_twoSq_isSub



theorem jic_twoSq_isCycles : jic_twoSq_P.G.IsCycles := by
  show jic_twoSq_G.IsCycles
  intro v _
  rw [Set.ncard_eq_two]
  fin_cases v
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jic_twoSq_rel] <;> decide⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jic_twoSq_rel] <;> decide⟩
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jic_twoSq_rel] <;> decide⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jic_twoSq_rel] <;> decide⟩
  · exact ⟨5, 7, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jic_twoSq_rel] <;> decide⟩
  · exact ⟨4, 6, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jic_twoSq_rel] <;> decide⟩
  · exact ⟨5, 7, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jic_twoSq_rel] <;> decide⟩
  · exact ⟨4, 6, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jic_twoSq_rel] <;> decide⟩




theorem jic_faithfulDiscreteJordan_twoSquares : whc_FaithfulDiscreteJordan jic_twoSq_P :=
  jic_faithfulDiscreteJordan jic_twoSq_P jic_twoSq_isCycles

end Lattice

end StatMech
