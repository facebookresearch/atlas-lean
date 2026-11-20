/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Percolation.HrouteHighDim
import Code.Walls.bkm_dccthreeaxes

open Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}












theorem bc2_rayCell_distinct_of_ne {i j : Fin d} (h : i ≠ j) {s t : ℤ} (hs : s ≠ 0) :
    (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t :=
  hrHD_rayPt_disjoint_of_ne h hs






theorem bc2_rayCell_distinct_of_ne' {i j : Fin d} (h : i ≠ j) {s t : ℤ} (ht : t ≠ 0) :
    (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t :=
  (hrHD_rayPt_disjoint_of_ne (Ne.symm h) ht).symm




theorem bc2_rayCell_eq_iff_origin {i j : Fin d} (h : i ≠ j) (s t : ℤ) :
    (hrHD_rayPt i s : Site d) = hrHD_rayPt j t ↔ (s = 0 ∧ t = 0) := by
  constructor
  · intro he
    have hi := congrFun he i
    rw [hrHD_rayPt_self, hrHD_rayPt_of_ne j t h] at hi
    have hj := congrFun he j
    rw [hrHD_rayPt_self, hrHD_rayPt_of_ne i s (Ne.symm h)] at hj
    exact ⟨hi, hj.symm⟩
  · rintro ⟨rfl, rfl⟩
    simp









def bc2_corridorVerts (j : Fin d) (L : ℕ) : Set (Site d) :=
  {x | ∃ e ∈ hrHD_corridorEdges j L, x ∈ e}



theorem bc2_corridorVerts_subset_corridorRay (j : Fin d) (L : ℕ) :
    bc2_corridorVerts j L ⊆ corridorRay j := by
  rintro x ⟨e, he, hxe⟩
  rw [hrHD_corridorEdges, Finset.mem_image] at he
  obtain ⟨t, _, rfl⟩ := he
  rw [Sym2.mem_iff] at hxe
  rcases hxe with rfl | rfl
  · exact rayPt_mem_corridorRay j _
  · exact rayPt_mem_corridorRay j _







theorem bc2_corridorVerts_inter_subset_origin {i j : Fin d} (h : i ≠ j) (L L' : ℕ) :
    bc2_corridorVerts i L ∩ bc2_corridorVerts j L' ⊆ {(0 : Site d)} := by
  rintro x ⟨hxi, hxj⟩
  have hmem : x ∈ corridorRay i ∩ corridorRay j :=
    ⟨bc2_corridorVerts_subset_corridorRay i L hxi,
     bc2_corridorVerts_subset_corridorRay j L' hxj⟩
  rwa [bkm_corridorRay_inter_eq_origin h] at hmem




theorem bc2_origin_mem_corridorVerts_iff (j : Fin d) (L : ℕ) :
    (0 : Site d) ∈ bc2_corridorVerts j L ↔ 0 < L := by
  constructor
  · rintro ⟨e, he, _⟩
    rw [hrHD_corridorEdges, Finset.mem_image] at he
    obtain ⟨t, ht, rfl⟩ := he
    exact Nat.lt_of_le_of_lt (Nat.zero_le t) (Finset.mem_range.mp ht)
  · intro hL
    refine ⟨s(hrHD_rayPt j (0 : ℤ), hrHD_rayPt j ((0 : ℤ) + 1)), hrHD_mem_corridorEdges hL, ?_⟩
    rw [Sym2.mem_iff]
    left
    simp















theorem bc2_corridorEdges_disjoint {i j : Fin d} (h : i ≠ j) (L L' : ℕ) :
    Disjoint (hrHD_corridorEdges i L) (hrHD_corridorEdges j L') := by
  rw [Finset.disjoint_left]
  intro e hei hej
  rw [hrHD_corridorEdges, Finset.mem_image] at hei hej
  obtain ⟨s, _, rfl⟩ := hei
  obtain ⟨t, _, hst⟩ := hej
  rw [Sym2.eq_iff] at hst
  have hsnz : ((s : ℤ) + 1) ≠ 0 := by positivity
  rcases hst with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact hrHD_rayPt_disjoint_of_ne h hsnz h2.symm
  · exact hrHD_rayPt_disjoint_of_ne h hsnz h1.symm













theorem bc2_ray_disjoint :
    ∀ {i j : Fin d}, i ≠ j → ∀ L L' : ℕ,
      (∀ s t : ℤ, s ≠ 0 → (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t) ∧
        Disjoint (hrHD_corridorEdges i L) (hrHD_corridorEdges j L') ∧
        bc2_corridorVerts i L ∩ bc2_corridorVerts j L' ⊆ {(0 : Site d)} :=
  fun h L L' =>
    ⟨fun _ _ hs => bc2_rayCell_distinct_of_ne h hs,
     bc2_corridorEdges_disjoint h L L',
     bc2_corridorVerts_inter_subset_origin h L L'⟩




theorem bc2_forced_corridors_share_only_origin {i j : Fin d} (h : i ≠ j) (L L' : ℕ) :
    Disjoint (hrHD_corridorEdges i L) (hrHD_corridorEdges j L') ∧
      (∀ x : Site d, x ≠ 0 → ¬ (x ∈ bc2_corridorVerts i L ∧ x ∈ bc2_corridorVerts j L')) := by
  refine ⟨bc2_corridorEdges_disjoint h L L', fun x hx hmem => hx ?_⟩
  exact Set.mem_singleton_iff.mp (bc2_corridorVerts_inter_subset_origin h L L' hmem)









theorem bc2_unit_cell_mem_corridorVerts (j : Fin d) {L : ℕ} (hL : 0 < L) :
    (hrHD_rayPt j 1 : Site d) ∈ bc2_corridorVerts j L ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 := by
  refine ⟨⟨s(hrHD_rayPt j (0 : ℤ), hrHD_rayPt j ((0 : ℤ) + 1)), hrHD_mem_corridorEdges hL, ?_⟩,
    by rw [Ne, hrHD_rayPt_eq_zero_iff]; exact one_ne_zero⟩
  rw [Sym2.mem_iff]; right; norm_num




theorem bc2_ray_disjoint_nonvacuous (hd : 2 ≤ d) :
    ∃ i j : Fin d, i ≠ j ∧
      (hrHD_rayPt i 1 : Site d) ≠ 0 ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 ∧
      (hrHD_rayPt i 1 : Site d) ≠ hrHD_rayPt j 1 ∧
      Disjoint (hrHD_corridorEdges i 1) (hrHD_corridorEdges j 1) ∧
      bc2_corridorVerts i 1 ∩ bc2_corridorVerts j 1 ⊆ {(0 : Site d)} := by
  have hij : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by intro h; simp [Fin.ext_iff] at h
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, hij, ?_, ?_, ?_, ?_, ?_⟩
  · exact (bc2_unit_cell_mem_corridorVerts _ one_pos).2
  · exact (bc2_unit_cell_mem_corridorVerts _ one_pos).2
  · exact bc2_rayCell_distinct_of_ne hij one_ne_zero
  · exact bc2_corridorEdges_disjoint hij 1 1
  · exact bc2_corridorVerts_inter_subset_origin hij 1 1

end StatMech.Walls
