/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Lattice.JordanEnclosureDuality
import Code.Walls.kwceventtocut
import Code.Walls.ceosimplecycle

open Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable











def jcw_shiftFace : Site 2 → Prop := fun f => f = ![0, 1]


theorem jcw_adj (x y x' y' : ℤ) (h : (x - x').natAbs + (y - y').natAbs = 1) :
    (hypercubicLattice 2).Adj (![x, y] : Site 2) (![x', y'] : Site 2) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega



theorem jcw_bottom_mem_cutSet :
    s((![0, 1] : Site 2), (![1, 1] : Site 2)) ∈ jed_cutSet jcw_shiftFace := by
  have hadj : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![0, 0] : Site 2) :=
    jcw_adj 0 1 0 0 (by norm_num)
  have hshared : sharedPrimalEdge (![0, 1] : Site 2) (![0, 0] : Site 2)
      = s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
    rw [show (![0, 0] : Site 2) = ![(0:ℤ), 1 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num
  rw [← hshared, jed_mem_cutSet_iff _ hadj]
  simp only [jcw_shiftFace, site2_eq]; norm_num



theorem jcw_right_mem_cutSet :
    s((![1, 1] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace := by
  have hadj : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) :=
    jcw_adj 0 1 1 1 (by norm_num)
  have hshared : sharedPrimalEdge (![0, 1] : Site 2) (![1, 1] : Site 2)
      = s((![1, 1] : Site 2), (![1, 2] : Site 2)) := by
    rw [show (![1, 1] : Site 2) = ![(0:ℤ) + 1, 1] by norm_num, sharedPrimalEdge_right]
    unfold faceCorner10 faceCorner11; norm_num
  rw [← hshared, jed_mem_cutSet_iff _ hadj]
  simp only [jcw_shiftFace, site2_eq]; norm_num



theorem jcw_top_mem_cutSet :
    s((![0, 2] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace := by
  have hadj : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![0, 2] : Site 2) :=
    jcw_adj 0 1 0 2 (by norm_num)
  have hshared : sharedPrimalEdge (![0, 1] : Site 2) (![0, 2] : Site 2)
      = s((![0, 2] : Site 2), (![1, 2] : Site 2)) := by
    rw [show (![0, 2] : Site 2) = ![(0:ℤ), 1 + 1] by norm_num, sharedPrimalEdge_top]
    unfold faceCorner01 faceCorner11; norm_num
  rw [← hshared, jed_mem_cutSet_iff _ hadj]
  simp only [jcw_shiftFace, site2_eq]; norm_num



theorem jcw_left_mem_cutSet :
    s((![0, 1] : Site 2), (![0, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace := by
  have hadj : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![-1, 1] : Site 2) :=
    jcw_adj 0 1 (-1) 1 (by norm_num)
  have hshared : sharedPrimalEdge (![0, 1] : Site 2) (![-1, 1] : Site 2)
      = s((![0, 1] : Site 2), (![0, 2] : Site 2)) := by
    rw [show (![-1, 1] : Site 2) = ![(0:ℤ) - 1, 1] by norm_num, sharedPrimalEdge_left]
    unfold faceCorner00 faceCorner01; norm_num
  rw [← hshared, jed_mem_cutSet_iff _ hadj]
  simp only [jcw_shiftFace, site2_eq]; norm_num














theorem jcw_shiftSquare_edges_subset_cutSet :
    s((![0, 1] : Site 2), (![1, 1] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧
    s((![1, 1] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧
    s((![0, 2] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧
    s((![0, 1] : Site 2), (![0, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace :=
  ⟨jcw_bottom_mem_cutSet, jcw_right_mem_cutSet, jcw_top_mem_cutSet, jcw_left_mem_cutSet⟩













theorem jcw_be_not_mem :
    s((![1, 1] : Site 2), (![2, 1] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

theorem jcw_cf_not_mem :
    s((![1, 2] : Site 2), (![2, 2] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

theorem jcw_ef_not_mem :
    s((![2, 1] : Site 2), (![2, 2] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]


theorem jcw_bc_mem :
    s((![1, 1] : Site 2), (![1, 2] : Site 2)) ∈ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]










theorem jcw_primalWalkBoundsRegion_false : ¬ PrimalWalkBoundsRegion := by
  intro hPWBR
  obtain ⟨S, hS⟩ := hPWBR ceo_shiftSquare
  
  have hbc : (hypercubicLattice 2).Adj (![1, 1] : Site 2) (![1, 2] : Site 2) :=
    jcw_adj 1 1 1 2 (by norm_num)
  have hbe : (hypercubicLattice 2).Adj (![1, 1] : Site 2) (![2, 1] : Site 2) :=
    jcw_adj 1 1 2 1 (by norm_num)
  have hcf : (hypercubicLattice 2).Adj (![1, 2] : Site 2) (![2, 2] : Site 2) :=
    jcw_adj 1 2 2 2 (by norm_num)
  have hef : (hypercubicLattice 2).Adj (![2, 1] : Site 2) (![2, 2] : Site 2) :=
    jcw_adj 2 1 2 2 (by norm_num)
  
  have hsplit : ((![1, 1] : Site 2) ∈ S ↔ (![1, 2] : Site 2) ∉ S) := by
    have := (hS hbc).mp (List.mem_toFinset.mpr jcw_bc_mem); rwa [bdEdge_mk] at this
  
  have heq_be : ((![1, 1] : Site 2) ∈ S ↔ (![2, 1] : Site 2) ∉ S) → False := by
    intro h; exact jcw_be_not_mem (List.mem_toFinset.mp ((hS hbe).mpr (by rw [bdEdge_mk]; exact h)))
  have heq_ef : ((![2, 1] : Site 2) ∈ S ↔ (![2, 2] : Site 2) ∉ S) → False := by
    intro h; exact jcw_ef_not_mem (List.mem_toFinset.mp ((hS hef).mpr (by rw [bdEdge_mk]; exact h)))
  have heq_cf : ((![1, 2] : Site 2) ∈ S ↔ (![2, 2] : Site 2) ∉ S) → False := by
    intro h; exact jcw_cf_not_mem (List.mem_toFinset.mp ((hS hcf).mpr (by rw [bdEdge_mk]; exact h)))
  
  by_cases hb : (![1, 1] : Site 2) ∈ S <;> by_cases hc : (![1, 2] : Site 2) ∈ S <;>
    by_cases he : (![2, 1] : Site 2) ∈ S <;> by_cases hf : (![2, 2] : Site 2) ∈ S <;>
    simp_all

























theorem jcw_status :
    
    (s((![0, 1] : Site 2), (![1, 1] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧
     s((![1, 1] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧
     s((![0, 2] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧
     s((![0, 1] : Site 2), (![0, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace) ∧
    
    (¬ PrimalWalkBoundsRegion) :=
  ⟨jcw_shiftSquare_edges_subset_cutSet, jcw_primalWalkBoundsRegion_false⟩

end Walls

end StatMech
