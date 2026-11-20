/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Mathlib
import Code.Percolation.HrouteHighDim
import Code.Percolation.HrouteDisjointPaths

open Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}








def corridorRay (j : Fin d) : Set (Site d) := {x | ∃ t : ℤ, x = hrHD_rayPt j t}


lemma origin_mem_corridorRay (j : Fin d) : (0 : Site d) ∈ corridorRay j :=
  ⟨0, by simp⟩


lemma rayPt_mem_corridorRay (j : Fin d) (t : ℤ) : hrHD_rayPt j t ∈ corridorRay j :=
  ⟨t, rfl⟩


lemma corridorEdge_subset_corridorRay {j : Fin d} (t : ℤ) :
    ∀ y ∈ (s(hrHD_rayPt j t, hrHD_rayPt j (t + 1)) : Sym2 (Site d)),
      y ∈ corridorRay j := by
  intro y hy
  rw [Sym2.mem_iff] at hy
  rcases hy with rfl | rfl
  · exact rayPt_mem_corridorRay j _
  · exact rayPt_mem_corridorRay j _








theorem bkm_three_axes_distinct (hd : 3 ≤ d) :
    (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ ∧
    (⟨0, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ ∧
    (⟨1, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · intro h; simp [Fin.ext_iff] at h










theorem bkm_corridorRay_inter_eq_origin {i j : Fin d} (h : i ≠ j) :
    corridorRay i ∩ corridorRay j = {(0 : Site d)} := by
  ext x
  simp only [Set.mem_inter_iff, corridorRay, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    by_cases hs : s = 0
    · subst hs; simp
    · exact absurd ht (hrHD_rayPt_disjoint_of_ne h hs)
  · rintro rfl
    exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩



theorem bkm_corridorRay_disjoint_off_origin {i j : Fin d} (h : i ≠ j) {x : Site d}
    (hx : x ≠ 0) : ¬ (x ∈ corridorRay i ∧ x ∈ corridorRay j) := by
  intro hmem
  have : x ∈ ({(0 : Site d)} : Set (Site d)) := by
    rw [← bkm_corridorRay_inter_eq_origin h]; exact hmem
  exact hx (Set.mem_singleton_iff.mp this)












theorem bkm_corridorEdges_disjoint_of_ne {i j : Fin d} (h : i ≠ j) (L : ℕ) :
    Disjoint (hrHD_corridorEdges i L) (hrHD_corridorEdges j L) := by
  rw [Finset.disjoint_left]
  intro e hei hej
  rw [hrHD_corridorEdges, Finset.mem_image] at hei hej
  obtain ⟨s, _, hse⟩ := hei
  obtain ⟨t, _, hte⟩ := hej
  
  have hj0 : ∀ y ∈ e, y i = 0 := by
    rw [← hte]
    intro y hy
    rw [Sym2.mem_iff] at hy
    rcases hy with rfl | rfl <;> exact hrHD_rayPt_of_ne j _ h
  
  have hmem : hrHD_rayPt i ((s : ℤ) + 1) ∈ e := by
    rw [← hse]; exact Sym2.mem_mk_right _ _
  have := hj0 _ hmem
  rw [hrHD_rayPt_self] at this
  omega














theorem bkm_dcc_three_axes (hd : 3 ≤ d) :
    ∃ j₁ j₂ j₃ : Fin d,
      (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
      (corridorRay j₁ ∩ corridorRay j₂ = {(0 : Site d)} ∧
        corridorRay j₁ ∩ corridorRay j₃ = {(0 : Site d)} ∧
        corridorRay j₂ ∩ corridorRay j₃ = {(0 : Site d)}) ∧
      (∀ L : ℕ, Disjoint (hrHD_corridorEdges j₁ L) (hrHD_corridorEdges j₂ L) ∧
        Disjoint (hrHD_corridorEdges j₁ L) (hrHD_corridorEdges j₃ L) ∧
        Disjoint (hrHD_corridorEdges j₂ L) (hrHD_corridorEdges j₃ L)) := by
  obtain ⟨j₁, j₂, j₃, h12, h13, h23⟩ := hrHD_exists_three_independent_axes hd
  exact ⟨j₁, j₂, j₃, ⟨h12, h13, h23⟩,
    ⟨bkm_corridorRay_inter_eq_origin h12, bkm_corridorRay_inter_eq_origin h13,
      bkm_corridorRay_inter_eq_origin h23⟩,
    fun L => ⟨bkm_corridorEdges_disjoint_of_ne h12 L, bkm_corridorEdges_disjoint_of_ne h13 L,
      bkm_corridorEdges_disjoint_of_ne h23 L⟩⟩

end StatMech.Walls
