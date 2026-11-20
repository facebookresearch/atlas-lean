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













theorem bc_rayCell_distinct_of_ne {i j : Fin d} (h : i ≠ j) {s t : ℤ} (hs : s ≠ 0) :
    (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t :=
  hrHD_rayPt_disjoint_of_ne h hs







theorem bc_rayCell_eq_iff_origin {i j : Fin d} (h : i ≠ j) (s t : ℤ) :
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














theorem bc_corridorRay_inter_eq_origin {i j : Fin d} (h : i ≠ j) :
    corridorRay i ∩ corridorRay j = {(0 : Site d)} := by
  ext x
  simp only [Set.mem_inter_iff, corridorRay, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    by_cases hs : s = 0
    · subst hs; simp
    · exact absurd ht (bc_rayCell_distinct_of_ne h hs)
  · rintro rfl
    exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩








theorem bc_corridors_share_only_origin {i j : Fin d} (h : i ≠ j) {x : Site d}
    (hx : x ≠ 0) : ¬ (x ∈ corridorRay i ∧ x ∈ corridorRay j) := by
  intro hmem
  have hxmem : x ∈ ({(0 : Site d)} : Set (Site d)) := by
    rw [← bc_corridorRay_inter_eq_origin h]; exact hmem
  exact hx (Set.mem_singleton_iff.mp hxmem)



















theorem bc_ray_disjoint :
    ∀ {i j : Fin d}, i ≠ j →
      (∀ s t : ℤ, s ≠ 0 → (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t) ∧
        corridorRay i ∩ corridorRay j = {(0 : Site d)} :=
  fun h => ⟨fun _ _ hs => bc_rayCell_distinct_of_ne h hs, bc_corridorRay_inter_eq_origin h⟩











theorem bc_unit_cell_mem_corridor_ne_origin (j : Fin d) :
    (hrHD_rayPt j 1 : Site d) ∈ corridorRay j ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 :=
  ⟨rayPt_mem_corridorRay j 1, by rw [Ne, hrHD_rayPt_eq_zero_iff]; exact one_ne_zero⟩




theorem bc_ray_disjoint_nonvacuous (hd : 2 ≤ d) :
    ∃ i j : Fin d, i ≠ j ∧
      (hrHD_rayPt i 1 : Site d) ≠ 0 ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 ∧
      (hrHD_rayPt i 1 : Site d) ≠ hrHD_rayPt j 1 ∧
      corridorRay i ∩ corridorRay j = {(0 : Site d)} := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [Fin.ext_iff] at h
  · exact (bc_unit_cell_mem_corridor_ne_origin _).2
  · exact (bc_unit_cell_mem_corridor_ne_origin _).2
  · exact bc_rayCell_distinct_of_ne (by intro h; simp [Fin.ext_iff] at h) one_ne_zero
  · exact bc_corridorRay_inter_eq_origin (by intro h; simp [Fin.ext_iff] at h)

end StatMech.Walls
