/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanEnclosureDuality
import Code.Lattice.JordanFaithfulCount
import Code.Walls.rpccrossflip
import Code.Walls.ceosimplecycle
import Code.Walls.dowdartwinding
import Code.Walls.kwceventtocut

open Set SimpleGraph
open scoped BigOperators

namespace StatMech
namespace Walls
open StatMech.Lattice












theorem fwr_sharedEdge_eq_crossEdge_horiz (x y : ℤ) :
    sharedPrimalEdge (![x, y] : Site 2) (![x + 1, y] : Site 2)
      = rpc_crossEdge (![x + 1, y + 1] : Site 2) (![x + 2, y + 1] : Site 2) := by
  rw [sharedPrimalEdge_right]
  unfold faceCorner10 faceCorner11 rpc_crossEdge
  rw [if_pos (by simp only [Matrix.cons_val_zero]; omega)]
  unfold rpc_hCrossEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  congr 2 <;>
    (funext i; fin_cases i <;>
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero] <;> omega)




theorem fwr_sharedEdge_eq_crossEdge_vert (x y : ℤ) :
    sharedPrimalEdge (![x, y] : Site 2) (![x, y + 1] : Site 2)
      = rpc_crossEdge (![x + 1, y + 1] : Site 2) (![x + 1, y + 2] : Site 2) := by
  rw [sharedPrimalEdge_top]
  unfold faceCorner01 faceCorner11 rpc_crossEdge
  rw [if_neg (by simp only [Matrix.cons_val_zero]; omega),
      if_neg (by simp only [Matrix.cons_val_zero]; omega),
      if_pos (by simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)]
  unfold rpc_vCrossEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [show (x + 1 - 1 : ℤ) = x by ring]







def fwr_faceInside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Site 2 → Prop :=
  fun f => ¬ Even (jec_rayCount (![f 0 + 1, f 1 + 1] : Site 2) Vc)


theorem fwr_faceInside_mk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (x y : ℤ) :
    fwr_faceInside Vc (![x, y] : Site 2)
      ↔ ¬ Even (jec_rayCount (![x + 1, y + 1] : Site 2) Vc) := by
  unfold fwr_faceInside
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]



theorem fwr_paritySwap (P Q : Prop) :
    ((¬ P) ↔ ¬ ¬ Q) ↔ ((¬ Q) ↔ ¬ ¬ P) := by
  constructor <;> intro h <;>
    · by_cases hp : P <;> by_cases hq : Q <;> simp_all




theorem fwr_faceCutFlip_aux_h {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c' d' : Site 2} (hcd : (hypercubicLattice 2).Adj c' d') :
    ((¬ Even (jec_rayCount c' Vc)) ↔ ¬ ¬ Even (jec_rayCount d' Vc))
      ↔ Odd (Vc.edges.count (rpc_crossEdge c' d')) := by
  have h := rpc_crossFlip Vc hcd
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion] at h
  exact h



theorem fwr_faceCutFlip_aux_v {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c' d' : Site 2} (hcd : (hypercubicLattice 2).Adj c' d') :
    ((¬ Even (jec_rayCount c' Vc)) ↔ ¬ ¬ Even (jec_rayCount d' Vc))
      ↔ Odd (Vc.edges.count (rpc_crossEdge c' d')) :=
  fwr_faceCutFlip_aux_h Vc hcd












theorem fwr_faceCutFlip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    (fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d)
      ↔ Odd (Vc.edges.count (sharedPrimalEdge c d)) := by
  classical
  
  set x := c 0 with hx
  set y := c 1 with hy
  have hc : c = ![x, y] := by funext i; fin_cases i <;> rfl
  have hcd' := hcd
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hcd'
  
  by_cases h0 : d 0 = c 0 + 1
  · 
    have hd0 : d 0 = x + 1 := by rw [hx]; omega
    have hd1 : d 1 = y := by rw [hy]; omega
    have hd : d = ![x + 1, y] := by
      funext i; fin_cases i
      · simpa using hd0
      · simpa using hd1
    have hc1 : (hypercubicLattice 2).Adj (![x + 1, y + 1] : Site 2) (![x + 2, y + 1] : Site 2) := by
      simp [hypercubicLattice_adj, Fin.sum_univ_two]
    rw [hc, hd, fwr_faceInside_mk, fwr_faceInside_mk, fwr_sharedEdge_eq_crossEdge_horiz]
    rw [show (x + 1 + 1 : ℤ) = x + 2 by ring]
    rw [← fwr_faceCutFlip_aux_h Vc hc1]
  · by_cases h0' : c 0 = d 0 + 1
    · 
      have hd0 : d 0 = x - 1 := by rw [hx]; omega
      have hd1 : d 1 = y := by rw [hy]; omega
      have hd : d = ![x - 1, y] := by
        funext i; fin_cases i
        · simpa using hd0
        · simpa using hd1
      have hc1 : (hypercubicLattice 2).Adj (![(x - 1) + 1, y + 1] : Site 2)
          (![(x - 1) + 2, y + 1] : Site 2) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
      have hshare : sharedPrimalEdge c d = sharedPrimalEdge (![x - 1, y] : Site 2)
          (![(x - 1) + 1, y] : Site 2) := by
        rw [hc, hd, sharedPrimalEdge_comm_of_adj (by
          rw [hypercubicLattice_adj, Fin.sum_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)]
        congr 2 <;> omega
      rw [hshare, fwr_sharedEdge_eq_crossEdge_horiz, hc, hd,
        fwr_faceInside_mk, fwr_faceInside_mk]
      have := fwr_faceCutFlip_aux_h Vc hc1
      
      rw [show ((x - 1) + 1 : ℤ) = x by ring, show ((x - 1) + 2 : ℤ) = x + 1 by ring] at this ⊢
      rw [← this]
      exact fwr_paritySwap _ _
    · 
      have hveq0 : d 0 = c 0 := by omega
      by_cases h1 : d 1 = c 1 + 1
      · 
        have hd0 : d 0 = x := by rw [hx]; exact hveq0
        have hd1 : d 1 = y + 1 := by rw [hy]; omega
        have hd : d = ![x, y + 1] := by
          funext i; fin_cases i
          · simpa using hd0
          · simpa using hd1
        have hc1 : (hypercubicLattice 2).Adj (![x + 1, y + 1] : Site 2)
            (![x + 1, y + 2] : Site 2) := by
          simp [hypercubicLattice_adj, Fin.sum_univ_two]
        rw [hc, hd, fwr_faceInside_mk, fwr_faceInside_mk, fwr_sharedEdge_eq_crossEdge_vert]
        rw [show (y + 1 + 1 : ℤ) = y + 2 by ring]
        rw [← fwr_faceCutFlip_aux_v Vc hc1]
      · 
        have hd0 : d 0 = x := by rw [hx]; exact hveq0
        have hd1 : d 1 = y - 1 := by rw [hy]; omega
        have hd : d = ![x, y - 1] := by
          funext i; fin_cases i
          · simpa using hd0
          · simpa using hd1
        have hc1 : (hypercubicLattice 2).Adj (![x + 1, (y - 1) + 1] : Site 2)
            (![x + 1, (y - 1) + 2] : Site 2) := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
        have hshare : sharedPrimalEdge c d = sharedPrimalEdge (![x, y - 1] : Site 2)
            (![x, (y - 1) + 1] : Site 2) := by
          rw [hc, hd, sharedPrimalEdge_comm_of_adj (by
            rw [hypercubicLattice_adj, Fin.sum_univ_two]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)]
          congr 2
          funext i; fin_cases i <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> omega
        rw [hshare, fwr_sharedEdge_eq_crossEdge_vert, hc, hd,
          fwr_faceInside_mk, fwr_faceInside_mk]
        have := fwr_faceCutFlip_aux_v Vc hc1
        rw [show ((y - 1) + 1 : ℤ) = y by ring, show ((y - 1) + 2 : ℤ) = y + 1 by ring] at this ⊢
        rw [← this]
        exact fwr_paritySwap _ _













theorem fwr_faceCutMatch_of_nodup {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    (fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d) ↔ sharedPrimalEdge c d ∈ Vc.edges := by
  rw [fwr_faceCutFlip Vc hcd]
  exact dow_odd_count_iff_mem_of_nodup hnd _






theorem fwr_jedCutSet_match_of_nodup {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    sharedPrimalEdge c d ∈ jed_cutSet (fwr_faceInside Vc) ↔ sharedPrimalEdge c d ∈ Vc.edges := by
  rw [jed_mem_cutSet_iff (fwr_faceInside Vc) hcd]
  
  exact fwr_faceCutMatch_of_nodup Vc hnd hcd












theorem fwr_primalWalkBoundsFaceRegion_of_nodup {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hnd : Vc.edges.Nodup)
    {u v : Site 2} (huv : (hypercubicLattice 2).Adj u v) :
    s(u, v) ∈ Vc.edges ↔ s(u, v) ∈ jed_cutSet (fwr_faceInside Vc) := by
  obtain ⟨f0, g0, hfg, hshared⟩ := jfc_flankingFaces huv
  rw [← hshared]
  exact (fwr_jedCutSet_match_of_nodup Vc hnd hfg).symm





def fwr_PrimalWalkBoundsFaceRegion : Prop :=
  ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), Vc.edges.Nodup →
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ Vc.edges ↔ s(u, v) ∈ jed_cutSet (fwr_faceInside Vc))





theorem fwr_primalWalkBoundsFaceRegion : fwr_PrimalWalkBoundsFaceRegion := by
  intro a Vc hnd u v huv
  exact fwr_primalWalkBoundsFaceRegion_of_nodup Vc hnd huv












theorem fwr_shiftSquare_faces_adj :
    (hypercubicLattice 2).Adj (![0, 0] : Site 2) (![0, 1] : Site 2) := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]



theorem fwr_shiftSquare_shared :
    sharedPrimalEdge (![0, 0] : Site 2) (![0, 1] : Site 2)
      = s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
  rw [show (![0, 1] : Site 2) = ![(0 : ℤ), 0 + 1] by norm_num, sharedPrimalEdge_top]
  unfold faceCorner01 faceCorner11; norm_num






theorem fwr_shiftSquare_faceCut_works :
    (fwr_faceInside ceo_shiftSquare (![0, 0] : Site 2)
      ↔ ¬ fwr_faceInside ceo_shiftSquare (![0, 1] : Site 2)) := by
  have hd : (fwr_faceInside ceo_shiftSquare (![0, 0] : Site 2)
      ↔ ¬ fwr_faceInside ceo_shiftSquare (![0, 1] : Site 2))
      ↔ sharedPrimalEdge (![0, 0] : Site 2) (![0, 1] : Site 2) ∈ ceo_shiftSquare.edges :=
    fwr_faceCutMatch_of_nodup ceo_shiftSquare ceo_shiftSquare_edges_nodup fwr_shiftSquare_faces_adj
  rw [hd, fwr_shiftSquare_shared]
  exact ceo_shiftSquare_edge_mem





theorem fwr_shiftSquare_rayCounts :
    jec_rayCount (![1, 1] : Site 2) ceo_shiftSquare = 0
      ∧ jec_rayCount (![1, 2] : Site 2) ceo_shiftSquare = 1 :=
  ⟨(ceo_shiftSquare_rayCount_endpoints).2, ceo_shiftSquare_inside_odd⟩











theorem fwr_shiftSquare_nonedge_left :
    s((![0, 0] : Site 2), (![0, 1] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

theorem fwr_shiftSquare_nonedge_bottom :
    s((![0, 0] : Site 2), (![1, 0] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

theorem fwr_shiftSquare_nonedge_right :
    s((![1, 0] : Site 2), (![1, 1] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]








theorem fwr_primalWalkBoundsRegion_false : ¬ PrimalWalkBoundsRegion := by
  intro h
  obtain ⟨S, hS⟩ := h ceo_shiftSquare
  have hadj_ab : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := ceo_uv_adj
  have hadj_a0 : (hypercubicLattice 2).Adj (![0, 0] : Site 2) (![0, 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hadj_01 : (hypercubicLattice 2).Adj (![0, 0] : Site 2) (![1, 0] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hadj_1b : (hypercubicLattice 2).Adj (![1, 0] : Site 2) (![1, 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  
  have hab : bdEdge S s((![0, 1] : Site 2), (![1, 1] : Site 2)) :=
    (hS hadj_ab).mp (List.mem_toFinset.mpr ceo_shiftSquare_edge_mem)
  
  have ha0 : ¬ bdEdge S s((![0, 0] : Site 2), (![0, 1] : Site 2)) := fun hbd =>
    fwr_shiftSquare_nonedge_left (List.mem_toFinset.mp ((hS hadj_a0).mpr hbd))
  have h01 : ¬ bdEdge S s((![0, 0] : Site 2), (![1, 0] : Site 2)) := fun hbd =>
    fwr_shiftSquare_nonedge_bottom (List.mem_toFinset.mp ((hS hadj_01).mpr hbd))
  have h1b : ¬ bdEdge S s((![1, 0] : Site 2), (![1, 1] : Site 2)) := fun hbd =>
    fwr_shiftSquare_nonedge_right (List.mem_toFinset.mp ((hS hadj_1b).mpr hbd))
  rw [bdEdge_mk] at hab ha0 h01 h1b
  
  by_cases m01 : (![0, 1] : Site 2) ∈ S <;> by_cases m11 : (![1, 1] : Site 2) ∈ S <;>
    by_cases m00 : (![0, 0] : Site 2) ∈ S <;> by_cases m10 : (![1, 0] : Site 2) ∈ S <;>
    simp_all






theorem fwr_faceCutMatch_nil {a : Site 2} {c d : Site 2}
    (hcd : (hypercubicLattice 2).Adj c d) :
    (fwr_faceInside (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a) c
      ↔ ¬ fwr_faceInside (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a) d)
      ↔ sharedPrimalEdge c d ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a).edges :=
  fwr_faceCutMatch_of_nodup _ (by simp) hcd







theorem fwr_scope {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    ((fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d)
      ↔ Odd (Vc.edges.count (sharedPrimalEdge c d)))
    ∧ (Vc.edges.Nodup →
      ((fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d) ↔ sharedPrimalEdge c d ∈ Vc.edges)) :=
  ⟨fwr_faceCutFlip Vc hcd, fun hnd => fwr_faceCutMatch_of_nodup Vc hnd hcd⟩

end Walls
end StatMech
