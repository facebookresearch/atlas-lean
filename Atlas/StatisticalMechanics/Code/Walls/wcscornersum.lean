/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Walls.wadangledefect
import Code.Lattice.EarContraction
import Code.Lattice.GaussBonnet
import Code.Walls.jc5_singlecycle

open scoped BigOperators
open Finset
open SimpleGraph Function

namespace StatMech

namespace Wcs

open StatMech.Lattice
open StatMech.Wad
open StatMech.Euc
open StatMech.Walls









def siteToVtx : Site 2 ≃ (ℤ × ℤ) where
  toFun := fun f => (f 0, f 1)
  invFun := fun p => ![p.1, p.2]
  left_inv := fun f => by funext i; fin_cases i <;> rfl
  right_inv := fun p => by rfl

@[simp] theorem siteToVtx_apply (f : Site 2) : siteToVtx f = (f 0, f 1) := rfl
@[simp] theorem siteToVtx_symm_apply (p : ℤ × ℤ) : siteToVtx.symm p = ![p.1, p.2] := rfl

@[simp] theorem siteToVtx_symm_zero (p : ℤ × ℤ) : (siteToVtx.symm p) 0 = p.1 := rfl
@[simp] theorem siteToVtx_symm_one (p : ℤ × ℤ) : (siteToVtx.symm p) 1 = p.2 := rfl


def toVtxSet (K : Set (Site 2)) : Set (ℤ × ℤ) := siteToVtx '' K

theorem mem_toVtxSet (K : Set (Site 2)) (p : ℤ × ℤ) :
    p ∈ toVtxSet K ↔ siteToVtx.symm p ∈ K := by
  unfold toVtxSet
  constructor
  · rintro ⟨s, hs, rfl⟩; rwa [Equiv.symm_apply_apply]
  · intro h; exact ⟨siteToVtx.symm p, h, by simp⟩

open Classical in


noncomputable def toVtxFinset (K : Set (Site 2)) (hK : K.Finite) : Finset (ℤ × ℤ) :=
  (hK.toFinset).image siteToVtx

theorem mem_toVtxFinset (K : Set (Site 2)) (hK : K.Finite) (p : ℤ × ℤ) :
    p ∈ toVtxFinset K hK ↔ siteToVtx.symm p ∈ K := by
  classical
  unfold toVtxFinset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Set.Finite.mem_toFinset] at hs
    rwa [Equiv.symm_apply_apply]
  · intro h
    exact ⟨siteToVtx.symm p, by rw [Set.Finite.mem_toFinset]; exact h, by simp⟩


theorem siteToVtx_mem_toVtxFinset (K : Set (Site 2)) (hK : K.Finite) (s : Site 2) :
    siteToVtx s ∈ toVtxFinset K hK ↔ s ∈ K := by
  rw [mem_toVtxFinset, Equiv.symm_apply_apply]











noncomputable def frontCell (e : Dart) : Site 2 := e.head + (-rot90Fun e.dir)

noncomputable def sideCell (e : Dart) : Site 2 := e.tail + (-rot90Fun e.dir)

open Classical in



theorem wcs_turnZ_probe (K : Set (Site 2)) (e : Dart) :
    turnZ K e =
      (if frontCell e ∈ K then 1 else if sideCell e ∈ K then 0 else -1) := by
  classical
  unfold turnZ frontCell sideCell; rfl


theorem wcs_turnZ_eq_one_iff (K : Set (Site 2)) (e : Dart) :
    turnZ K e = 1 ↔ frontCell e ∈ K := by
  classical
  rw [wcs_turnZ_probe]
  by_cases h : frontCell e ∈ K
  · simp [h]
  · simp only [h, if_false, iff_false]
    by_cases h2 : sideCell e ∈ K <;> simp [h2]


theorem wcs_turnZ_eq_negone_iff (K : Set (Site 2)) (e : Dart) :
    turnZ K e = -1 ↔ (frontCell e ∉ K ∧ sideCell e ∉ K) := by
  classical
  rw [wcs_turnZ_probe]
  by_cases h1 : frontCell e ∈ K
  · simp [h1]
  · by_cases h2 : sideCell e ∈ K
    · simp [h1, h2]
    · simp [h1, h2]


theorem wcs_turnZ_eq_zero_iff (K : Set (Site 2)) (e : Dart) :
    turnZ K e = 0 ↔ (frontCell e ∉ K ∧ sideCell e ∈ K) := by
  classical
  rw [wcs_turnZ_probe]
  by_cases h1 : frontCell e ∈ K
  · simp [h1]
  · by_cases h2 : sideCell e ∈ K
    · simp [h1, h2]
    · simp [h1, h2]












noncomputable def posPartSite (z : Site 2) : Site 2 := ![max (z 0) 0, max (z 1) 0]



noncomputable def wcs_pivotSite (e : Dart) : Site 2 :=
  e.tail + posPartSite e.dir + posPartSite (-rot90Fun e.dir)


noncomputable def wcs_pivot (e : Dart) : ℤ × ℤ := siteToVtx (wcs_pivotSite e)


theorem wcs_dir_cases (e : Dart) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
  have hadj := e.adj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have key : ((e.dir 0).natAbs = 1 ∧ (e.dir 1).natAbs = 0) ∨
             ((e.dir 0).natAbs = 0 ∧ (e.dir 1).natAbs = 1) := by
    have hd : e.dir = e.head - e.tail := rfl
    rw [hd]; simp only [Pi.sub_apply]; omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rcases Int.natAbs_eq_iff.mp h0 with h | h
    · left; funext i; fin_cases i <;> simp_all [Dart.dir]
    · right; left; funext i; fin_cases i <;> simp_all [Dart.dir]
  · rcases Int.natAbs_eq_iff.mp h1 with h | h
    · right; right; left; funext i; fin_cases i <;> simp_all [Dart.dir]
    · right; right; right; funext i; fin_cases i <;> simp_all [Dart.dir]


theorem siteToVtx_add (x y : Site 2) :
    siteToVtx (x + y) = (siteToVtx x + siteToVtx y) := by
  simp only [siteToVtx_apply, Pi.add_apply, Prod.mk_add_mk]





theorem wcs_surroundCells_pivot (e : Dart) :
    surroundCells (wcs_pivot e) =
      ({siteToVtx e.tail, siteToVtx e.head, siteToVtx (sideCell e),
        siteToVtx (frontCell e)} : Finset (ℤ × ℤ)) := by
  have hhead : e.head = e.tail + e.dir := by
    rw [Dart.dir_def]; abel
  unfold wcs_pivot wcs_pivotSite sideCell frontCell posPartSite surroundCells
  rw [hhead]
  set a : ℤ := e.tail 0 with ha
  set b : ℤ := e.tail 1 with hb
  rcases wcs_dir_cases e with hd | hd | hd | hd <;>
    · rw [hd]
      simp only [siteToVtx_apply, Pi.add_apply, Pi.neg_apply, rot90Fun_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        neg_neg, neg_zero, max_self]
      rw [← ha, ← hb]
      ext p
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      norm_num
      omega



theorem wcs_block_pairwise_distinct (e : Dart) :
    (siteToVtx e.tail ≠ siteToVtx e.head) ∧
    (siteToVtx e.tail ≠ siteToVtx (sideCell e)) ∧
    (siteToVtx e.tail ≠ siteToVtx (frontCell e)) ∧
    (siteToVtx e.head ≠ siteToVtx (sideCell e)) ∧
    (siteToVtx e.head ≠ siteToVtx (frontCell e)) ∧
    (siteToVtx (sideCell e) ≠ siteToVtx (frontCell e)) := by
  have hhead : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
  unfold sideCell frontCell
  rw [hhead]
  set a : ℤ := e.tail 0 with ha
  set b : ℤ := e.tail 1 with hb
  rcases wcs_dir_cases e with hd | hd | hd | hd <;>
    · rw [hd]
      simp only [siteToVtx_apply, Pi.add_apply, Pi.neg_apply, rot90Fun_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        neg_neg, neg_zero, ne_eq, Prod.ext_iff, not_and]
      rw [← ha, ← hb]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> omega















theorem wcs_edgeDeg_formula (K' : Finset (ℤ × ℤ)) (x y : ℤ) :
    (edgeDeg K' (x, y) : ℤ) =
      (if (((x, y) ∈ K') ∨ ((x, y - 1) ∈ K')) then 1 else 0)
        + (if (((x - 1, y) ∈ K') ∨ ((x - 1, y - 1) ∈ K')) then 1 else 0)
        + (if (((x - 1, y) ∈ K') ∨ ((x, y) ∈ K')) then 1 else 0)
        + (if (((x - 1, y - 1) ∈ K') ∨ ((x, y - 1) ∈ K')) then 1 else 0) := by
  classical
  rw [wad_edgeDeg_eq, Finset.card_filter]
  have i1 : incidentEdgeR (x, y) ∉
      ({incidentEdgeL (x, y), incidentEdgeU (x, y), incidentEdgeD (x, y)} :
        Finset (Sym2 (ℤ × ℤ))) := by
    simp only [incidentEdgeR, incidentEdgeL, incidentEdgeU, incidentEdgeD, Finset.mem_insert,
      Finset.mem_singleton, Sym2.eq_iff, Prod.mk.injEq]; push_neg; refine ⟨?_, ?_, ?_⟩ <;> omega
  have i2 : incidentEdgeL (x, y) ∉
      ({incidentEdgeU (x, y), incidentEdgeD (x, y)} : Finset (Sym2 (ℤ × ℤ))) := by
    simp only [incidentEdgeL, incidentEdgeU, incidentEdgeD, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff, Prod.mk.injEq]; push_neg; refine ⟨?_, ?_⟩ <;> omega
  have i3 : incidentEdgeU (x, y) ∉ ({incidentEdgeD (x, y)} : Finset (Sym2 (ℤ × ℤ))) := by
    simp only [incidentEdgeD, incidentEdgeU, Finset.mem_singleton, Sym2.eq_iff, Prod.mk.injEq]
    push_neg; omega
  rw [Finset.sum_insert i1, Finset.sum_insert i2, Finset.sum_insert i3, Finset.sum_singleton]
  simp only [wad_incidentR_mem, wad_incidentL_mem, wad_incidentU_mem, wad_incidentD_mem]
  push_cast; ring










theorem wcs_edgeDeg_pivot (K : Set (Site 2)) (hK : K.Finite) (e : Dart) :
    (edgeDeg (toVtxFinset K hK) (wcs_pivot e) : ℤ) =
      (if (siteToVtx e.tail ∈ toVtxFinset K hK ∨ siteToVtx e.head ∈ toVtxFinset K hK)
        then 1 else 0)
      + (if (siteToVtx e.tail ∈ toVtxFinset K hK ∨ siteToVtx (sideCell e) ∈ toVtxFinset K hK)
        then 1 else 0)
      + (if (siteToVtx e.head ∈ toVtxFinset K hK ∨ siteToVtx (frontCell e) ∈ toVtxFinset K hK)
        then 1 else 0)
      + (if (siteToVtx (sideCell e) ∈ toVtxFinset K hK ∨ siteToVtx (frontCell e) ∈ toVtxFinset K hK)
        then 1 else 0) := by
  classical
  set K' := toVtxFinset K hK with hK'
  have hhead : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
  
  have key : wcs_pivot e = ((wcs_pivot e).1, (wcs_pivot e).2) := rfl
  rw [key, wcs_edgeDeg_formula K']
  
  unfold wcs_pivot wcs_pivotSite sideCell frontCell posPartSite
  rw [hhead]
  set a : ℤ := e.tail 0 with ha
  set b : ℤ := e.tail 1 with hb
  rcases wcs_dir_cases e with hd | hd | hd | hd <;>
    · rw [hd]
      simp only [siteToVtx_apply, Pi.add_apply, Pi.neg_apply, rot90Fun_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        neg_neg, neg_zero, max_self, max_eq_left, max_eq_right, le_refl]
      rw [← ha, ← hb]
      norm_num
      simp (config := { failIfUnchanged := false }) only [or_comm]
      ring_nf





theorem wcs_cellDeg_pivot (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (hb : IsBoundaryDart K e) :
    cellDeg (toVtxFinset K hK) (wcs_pivot e) =
      (if siteToVtx (sideCell e) ∈ toVtxFinset K hK then 1 else 0)
        + (if siteToVtx (frontCell e) ∈ toVtxFinset K hK then 1 else 0) + 1 := by
  classical
  unfold cellDeg
  rw [wcs_surroundCells_pivot]
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := wcs_block_pairwise_distinct e
  set K' := toVtxFinset K hK with hK'
  have mt : siteToVtx e.tail ∈ K' := (siteToVtx_mem_toVtxFinset K hK _).mpr hb.1
  have mh : siteToVtx e.head ∉ K' := by
    rw [hK', siteToVtx_mem_toVtxFinset K hK]; exact hb.2
  
  rw [Finset.filter_mem_eq_inter.symm]
  
  rw [show ({siteToVtx e.tail, siteToVtx e.head, siteToVtx (sideCell e),
      siteToVtx (frontCell e)} : Finset (ℤ × ℤ)).filter (· ∈ K')
      = (({siteToVtx e.tail, siteToVtx e.head, siteToVtx (sideCell e),
      siteToVtx (frontCell e)} : Finset (ℤ × ℤ)).filter (· ∈ K')) from rfl]
  rw [Finset.card_filter]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; tauto),
      Finset.sum_singleton]
  simp only [mt, mh, if_true, if_false]
  ring




theorem wcs_pivot_mem_regVerts (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (hb : IsBoundaryDart K e) :
    wcs_pivot e ∈ regVerts (toVtxFinset K hK) := by
  classical
  have hmem : siteToVtx e.tail ∈ surroundCells (wcs_pivot e) := by
    rw [wcs_surroundCells_pivot]; simp
  rw [wad_mem_surround_iff] at hmem
  unfold regVerts
  rw [Finset.mem_biUnion]
  exact ⟨siteToVtx e.tail, (siteToVtx_mem_toVtxFinset K hK _).mpr hb.1, hmem⟩

open Classical in













theorem wcs_defect_pivot_eq (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (hb : IsBoundaryDart K e) :
    defect (toVtxFinset K hK) (wcs_pivot e) =
      (if frontCell e ∈ K then
        if sideCell e ∈ K then -1 else -2
      else if sideCell e ∈ K then 0 else 1) := by
  classical
  have mt : siteToVtx e.tail ∈ toVtxFinset K hK :=
    (siteToVtx_mem_toVtxFinset K hK _).mpr hb.1
  have mh : siteToVtx e.head ∉ toVtxFinset K hK := by
    rw [siteToVtx_mem_toVtxFinset K hK]
    exact hb.2
  have ms : siteToVtx (sideCell e) ∈ toVtxFinset K hK ↔ sideCell e ∈ K :=
    siteToVtx_mem_toVtxFinset K hK _
  have mf : siteToVtx (frontCell e) ∈ toVtxFinset K hK ↔ frontCell e ∈ K :=
    siteToVtx_mem_toVtxFinset K hK _
  have hcd := wcs_cellDeg_pivot K hK e hb
  have hed := wcs_edgeDeg_pivot K hK e
  have hdefeq : (defect (toVtxFinset K hK) (wcs_pivot e) : ℤ) =
      4 - 2 * (edgeDeg (toVtxFinset K hK) (wcs_pivot e) : ℤ)
        + (cellDeg (toVtxFinset K hK) (wcs_pivot e) : ℤ) := rfl
  rw [hdefeq, hcd, hed]
  
  simp only [mt, mh, ms, mf, true_or, false_or, if_true]
  by_cases hf : frontCell e ∈ K <;> by_cases hs : sideCell e ∈ K <;>
    simp only [hf, hs, if_true, if_false, true_or, or_true, and_true, and_false, true_and,
      false_and, or_self] <;> push_cast <;> ring











theorem wcs_turnZ_eq_neg_defect_of_pivot (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (hb : IsBoundaryDart K e) (hnp : ¬(frontCell e ∈ K ∧ sideCell e ∉ K)) :
    turnZ K e = - defect (toVtxFinset K hK) (wcs_pivot e) := by
  classical
  rw [wcs_turnZ_probe, wcs_defect_pivot_eq K hK e hb]
  by_cases hf : frontCell e ∈ K
  · by_cases hs : sideCell e ∈ K
    · simp [hf, hs]
    · exact (hnp ⟨hf, hs⟩).elim
  · by_cases hs : sideCell e ∈ K <;> simp [hf, hs]

end Wcs

end StatMech
