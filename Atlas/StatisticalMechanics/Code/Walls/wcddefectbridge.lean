/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib
import Code.Walls.wadangledefect
import Code.Walls.jc5_singlecycle
import Code.Lattice.EarContraction
import Code.Lattice.BalanceContraction
import Code.Lattice.GaussBonnet
import Code.Lattice.TurningNumber

open scoped BigOperators
open Finset
open SimpleGraph Function

namespace StatMech

namespace Wcd

open StatMech.Lattice
open StatMech.Wad
open StatMech.Euc




def wcd_siteToVtx : Site 2 ≃ (ℤ × ℤ) where
  toFun := fun f => (f 0, f 1)
  invFun := fun p => ![p.1, p.2]
  left_inv := fun f => by funext i; fin_cases i <;> rfl
  right_inv := fun p => by rfl

@[simp] theorem wcd_siteToVtx_apply (f : Site 2) : wcd_siteToVtx f = (f 0, f 1) := rfl

open Classical in

noncomputable def wcd_toVtxFinset (K : Set (Site 2)) (hK : K.Finite) : Finset (ℤ × ℤ) :=
  (hK.toFinset).image wcd_siteToVtx

theorem wcd_mem_toVtxFinset (K : Set (Site 2)) (hK : K.Finite) (p : ℤ × ℤ) :
    p ∈ wcd_toVtxFinset K hK ↔ wcd_siteToVtx.symm p ∈ K := by
  classical
  unfold wcd_toVtxFinset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Set.Finite.mem_toFinset] at hs
    rwa [Equiv.symm_apply_apply]
  · intro h
    exact ⟨wcd_siteToVtx.symm p, by rw [Set.Finite.mem_toFinset]; exact h, by simp⟩


theorem wcd_siteToVtx_mem_toVtxFinset (K : Set (Site 2)) (hK : K.Finite) (s : Site 2) :
    wcd_siteToVtx s ∈ wcd_toVtxFinset K hK ↔ s ∈ K := by
  rw [wcd_mem_toVtxFinset, Equiv.symm_apply_apply]




noncomputable def wcd_frontCell (e : Dart) : Site 2 := e.head + (-rot90Fun e.dir)

noncomputable def wcd_sideCell (e : Dart) : Site 2 := e.tail + (-rot90Fun e.dir)

open Classical in

theorem wcd_turnZ_probe (K : Set (Site 2)) (e : Dart) :
    turnZ K e =
      (if wcd_frontCell e ∈ K then 1 else if wcd_sideCell e ∈ K then 0 else -1) := by
  classical
  unfold turnZ wcd_frontCell wcd_sideCell; rfl




noncomputable def wcd_posPartSite (z : Site 2) : Site 2 := ![max (z 0) 0, max (z 1) 0]


noncomputable def wcd_pivotSite (e : Dart) : Site 2 :=
  e.tail + wcd_posPartSite e.dir + wcd_posPartSite (-rot90Fun e.dir)


noncomputable def wcd_pivot (e : Dart) : ℤ × ℤ := wcd_siteToVtx (wcd_pivotSite e)


theorem wcd_dir_cases (e : Dart) :
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



theorem wcd_surroundCells_pivot (e : Dart) :
    surroundCells (wcd_pivot e) =
      ({wcd_siteToVtx e.tail, wcd_siteToVtx e.head, wcd_siteToVtx (wcd_sideCell e),
        wcd_siteToVtx (wcd_frontCell e)} : Finset (ℤ × ℤ)) := by
  have hhead : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
  unfold wcd_pivot wcd_pivotSite wcd_sideCell wcd_frontCell wcd_posPartSite surroundCells
  rw [hhead]
  set a : ℤ := e.tail 0 with ha
  set b : ℤ := e.tail 1 with hb
  rcases wcd_dir_cases e with hd | hd | hd | hd <;>
    · rw [hd]
      simp only [wcd_siteToVtx_apply, Pi.add_apply, Pi.neg_apply, rot90Fun_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        neg_neg, neg_zero, max_self]
      rw [← ha, ← hb]
      ext p
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      norm_num
      omega


theorem wcd_block_pairwise_distinct (e : Dart) :
    (wcd_siteToVtx e.tail ≠ wcd_siteToVtx e.head) ∧
    (wcd_siteToVtx e.tail ≠ wcd_siteToVtx (wcd_sideCell e)) ∧
    (wcd_siteToVtx e.tail ≠ wcd_siteToVtx (wcd_frontCell e)) ∧
    (wcd_siteToVtx e.head ≠ wcd_siteToVtx (wcd_sideCell e)) ∧
    (wcd_siteToVtx e.head ≠ wcd_siteToVtx (wcd_frontCell e)) ∧
    (wcd_siteToVtx (wcd_sideCell e) ≠ wcd_siteToVtx (wcd_frontCell e)) := by
  have hhead : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
  unfold wcd_sideCell wcd_frontCell
  rw [hhead]
  set a : ℤ := e.tail 0 with ha
  set b : ℤ := e.tail 1 with hb
  rcases wcd_dir_cases e with hd | hd | hd | hd <;>
    · rw [hd]
      simp only [wcd_siteToVtx_apply, Pi.add_apply, Pi.neg_apply, rot90Fun_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        neg_neg, neg_zero, ne_eq, Prod.ext_iff, not_and]
      rw [← ha, ← hb]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> omega




theorem wcd_edgeDeg_formula (K' : Finset (ℤ × ℤ)) (x y : ℤ) :
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


theorem wcd_edgeDeg_pivot (K : Set (Site 2)) (hK : K.Finite) (e : Dart) :
    (edgeDeg (wcd_toVtxFinset K hK) (wcd_pivot e) : ℤ) =
      (if (wcd_siteToVtx e.tail ∈ wcd_toVtxFinset K hK ∨ wcd_siteToVtx e.head ∈ wcd_toVtxFinset K hK)
        then 1 else 0)
      + (if (wcd_siteToVtx e.tail ∈ wcd_toVtxFinset K hK ∨ wcd_siteToVtx (wcd_sideCell e) ∈ wcd_toVtxFinset K hK)
        then 1 else 0)
      + (if (wcd_siteToVtx e.head ∈ wcd_toVtxFinset K hK ∨ wcd_siteToVtx (wcd_frontCell e) ∈ wcd_toVtxFinset K hK)
        then 1 else 0)
      + (if (wcd_siteToVtx (wcd_sideCell e) ∈ wcd_toVtxFinset K hK ∨ wcd_siteToVtx (wcd_frontCell e) ∈ wcd_toVtxFinset K hK)
        then 1 else 0) := by
  classical
  set K' := wcd_toVtxFinset K hK with hK'
  have hhead : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
  have key : wcd_pivot e = ((wcd_pivot e).1, (wcd_pivot e).2) := rfl
  rw [key, wcd_edgeDeg_formula K']
  unfold wcd_pivot wcd_pivotSite wcd_sideCell wcd_frontCell wcd_posPartSite
  rw [hhead]
  set a : ℤ := e.tail 0 with ha
  set b : ℤ := e.tail 1 with hb
  rcases wcd_dir_cases e with hd | hd | hd | hd <;>
    · rw [hd]
      simp only [wcd_siteToVtx_apply, Pi.add_apply, Pi.neg_apply, rot90Fun_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        neg_neg, neg_zero, max_self, max_eq_left, max_eq_right, le_refl]
      rw [← ha, ← hb]
      norm_num
      simp only [sub_eq_add_neg, or_comm, or_left_comm, or_assoc]
      abel





theorem wcd_cellDeg_pivot (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (hb : IsBoundaryDart K e) :
    cellDeg (wcd_toVtxFinset K hK) (wcd_pivot e) =
      (if wcd_siteToVtx (wcd_sideCell e) ∈ wcd_toVtxFinset K hK then 1 else 0)
        + (if wcd_siteToVtx (wcd_frontCell e) ∈ wcd_toVtxFinset K hK then 1 else 0) + 1 := by
  classical
  unfold cellDeg
  rw [wcd_surroundCells_pivot]
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := wcd_block_pairwise_distinct e
  set K' := wcd_toVtxFinset K hK with hK'
  have mt : wcd_siteToVtx e.tail ∈ K' := (wcd_siteToVtx_mem_toVtxFinset K hK _).mpr hb.1
  have mh : wcd_siteToVtx e.head ∉ K' := by
    rw [hK', wcd_siteToVtx_mem_toVtxFinset K hK]; exact hb.2
  rw [Finset.filter_mem_eq_inter.symm]
  rw [Finset.card_filter]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; tauto),
      Finset.sum_singleton]
  simp only [mt, mh, if_true, if_false]
  ring


theorem wcd_pivot_mem_regVerts (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (hb : IsBoundaryDart K e) :
    wcd_pivot e ∈ regVerts (wcd_toVtxFinset K hK) := by
  classical
  have hmem : wcd_siteToVtx e.tail ∈ surroundCells (wcd_pivot e) := by
    rw [wcd_surroundCells_pivot]; simp
  rw [wad_mem_surround_iff] at hmem
  unfold regVerts
  rw [Finset.mem_biUnion]
  exact ⟨wcd_siteToVtx e.tail, (wcd_siteToVtx_mem_toVtxFinset K hK _).mpr hb.1, hmem⟩

open Classical in







theorem wcd_defect_pivot_eq (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (hb : IsBoundaryDart K e) :
    defect (wcd_toVtxFinset K hK) (wcd_pivot e) =
      (if wcd_frontCell e ∈ K then (if wcd_sideCell e ∈ K then -1 else -2)
       else (if wcd_sideCell e ∈ K then 0 else 1)) := by
  classical
  have mt : wcd_siteToVtx e.tail ∈ wcd_toVtxFinset K hK :=
    (wcd_siteToVtx_mem_toVtxFinset K hK _).mpr hb.1
  have mh : wcd_siteToVtx e.head ∉ wcd_toVtxFinset K hK := by
    rw [wcd_siteToVtx_mem_toVtxFinset K hK]; exact hb.2
  have ms : wcd_siteToVtx (wcd_sideCell e) ∈ wcd_toVtxFinset K hK ↔ wcd_sideCell e ∈ K :=
    wcd_siteToVtx_mem_toVtxFinset K hK _
  have mf : wcd_siteToVtx (wcd_frontCell e) ∈ wcd_toVtxFinset K hK ↔ wcd_frontCell e ∈ K :=
    wcd_siteToVtx_mem_toVtxFinset K hK _
  have hcd := wcd_cellDeg_pivot K hK e hb
  have hed := wcd_edgeDeg_pivot K hK e
  have hdefeq : (defect (wcd_toVtxFinset K hK) (wcd_pivot e) : ℤ)
      = 4 - 2 * (edgeDeg (wcd_toVtxFinset K hK) (wcd_pivot e) : ℤ)
        + (cellDeg (wcd_toVtxFinset K hK) (wcd_pivot e) : ℤ) := rfl
  rw [hdefeq, hcd, hed]
  by_cases hf : wcd_frontCell e ∈ K <;> by_cases hs : wcd_sideCell e ∈ K <;>
    simp only [mt, mh, ms, mf, hf, hs, if_true, if_false, or_true, or_false,
      or_self] <;> push_cast <;> omega

open Classical in





theorem wcd_turnZ_eq_neg_defect_of_pivot (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (hb : IsBoundaryDart K e) (hnp : ¬(wcd_frontCell e ∈ K ∧ wcd_sideCell e ∉ K)) :
    turnZ K e = - defect (wcd_toVtxFinset K hK) (wcd_pivot e) := by
  classical
  rw [wcd_turnZ_probe, wcd_defect_pivot_eq K hK e hb]
  by_cases hf : wcd_frontCell e ∈ K
  · by_cases hs : wcd_sideCell e ∈ K
    · simp only [hf, hs, if_true]; omega
    · exact absurd ⟨hf, hs⟩ hnp
  · by_cases hs : wcd_sideCell e ∈ K <;>
      simp only [hf, hs, if_true, if_false] <;> omega








theorem wcd_cornerBalance_eq_neg_pivotSum (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hpf : ∀ i < dartOrbitPeriod K a,
      ¬(wcd_frontCell ((dartNext K)^[i] a.1) ∈ K ∧ wcd_sideCell ((dartNext K)^[i] a.1) ∉ K)) :
    cornerBalance K a =
      - ∑ i ∈ Finset.range (dartOrbitPeriod K a),
          defect (wcd_toVtxFinset K hK) (wcd_pivot ((dartNext K)^[i] a.1)) := by
  have hsum : totalTurnZ K a.1 (dartOrbitPeriod K a)
      = ∑ i ∈ Finset.range (dartOrbitPeriod K a),
          (- defect (wcd_toVtxFinset K hK) (wcd_pivot ((dartNext K)^[i] a.1))) := by
    unfold totalTurnZ
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact wcd_turnZ_eq_neg_defect_of_pivot K hK ((dartNext K)^[i] a.1)
      (iterate_isBoundaryDart K a.1 a.2 i) (hpf i hi)
  rw [cornerBalance_eq_totalTurnZ, hsum, Finset.sum_neg_distrib]






theorem wcd_pivotSum_eq_regVertsSum (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hinj : Set.InjOn (fun i => wcd_pivot ((dartNext K)^[i] a.1))
      (Set.Iio (dartOrbitPeriod K a)))
    (hcov : ∀ v ∈ regVerts (wcd_toVtxFinset K hK),
      v ∉ (Finset.range (dartOrbitPeriod K a)).image
        (fun i => wcd_pivot ((dartNext K)^[i] a.1)) →
      defect (wcd_toVtxFinset K hK) v = 0) :
    ∑ i ∈ Finset.range (dartOrbitPeriod K a),
        defect (wcd_toVtxFinset K hK) (wcd_pivot ((dartNext K)^[i] a.1))
      = ∑ v ∈ regVerts (wcd_toVtxFinset K hK), defect (wcd_toVtxFinset K hK) v := by
  classical
  set f : ℕ → ℤ × ℤ := fun i => wcd_pivot ((dartNext K)^[i] a.1) with hf
  have hinj' : ∀ x ∈ Finset.range (dartOrbitPeriod K a), ∀ y ∈ Finset.range (dartOrbitPeriod K a),
      f x = f y → x = y := by
    intro x hx y hy hxy
    exact hinj (Set.mem_Iio.mpr (Finset.mem_range.mp hx))
      (Set.mem_Iio.mpr (Finset.mem_range.mp hy)) hxy
  rw [← Finset.sum_image hinj']
  apply Finset.sum_subset
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨i, _, rfl⟩ := hv
    exact wcd_pivot_mem_regVerts K hK _ (iterate_isBoundaryDart K a.1 a.2 i)
  · exact hcov












def WcdPivotBridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  (∀ i < dartOrbitPeriod K a,
      ¬(wcd_frontCell ((dartNext K)^[i] a.1) ∈ K ∧ wcd_sideCell ((dartNext K)^[i] a.1) ∉ K)) ∧
  (Set.InjOn (fun i => wcd_pivot ((dartNext K)^[i] a.1)) (Set.Iio (dartOrbitPeriod K a))) ∧
  (∀ v ∈ regVerts (wcd_toVtxFinset K hK),
      v ∉ (Finset.range (dartOrbitPeriod K a)).image
        (fun i => wcd_pivot ((dartNext K)^[i] a.1)) →
      defect (wcd_toVtxFinset K hK) v = 0)


theorem wcd_cornerBalance_eq_neg_defectSum (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hbr : WcdPivotBridge K hK a) :
    cornerBalance K a
      = - ∑ v ∈ regVerts (wcd_toVtxFinset K hK), defect (wcd_toVtxFinset K hK) v := by
  obtain ⟨hpf, hinj, hcov⟩ := hbr
  rw [wcd_cornerBalance_eq_neg_pivotSum K hK a hpf,
    wcd_pivotSum_eq_regVertsSum K hK a hinj hcov]



theorem wcd_cornerBalance_eq_neg_four (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hbr : WcdPivotBridge K hK a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    cornerBalance K a = -4 := by
  rw [wcd_cornerBalance_eq_neg_defectSum K hK a hbr, wad_defect_eq_four_chi,
    euc_chi_induction hbuild]
  norm_num


theorem wcd_revCount_eq_neg_one (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hbr : WcdPivotBridge K hK a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    revCount K a = -1 := by
  have h := wcd_cornerBalance_eq_neg_four K hK a hbr hbuild
  have h2 := cornerBalance_eq_four_revCount K a
  rw [h] at h2
  omega


theorem wcd_revCount_pm_one (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hbr : WcdPivotBridge K hK a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  Or.inr (wcd_revCount_eq_neg_one K hK a hbr hbuild)




theorem wcd_balanceIsFour (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hbr : WcdPivotBridge K hK a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    BalanceIsFour K a :=
  (balanceIsFour_iff_revCount_pm_one K a).mpr (wcd_revCount_pm_one K hK a hbr hbuild)




theorem wcd_unitCell_finite : unitCell.Finite := by
  unfold unitCell; exact Set.finite_singleton _


theorem wcd_toVtxFinset_unitCell (hfin : unitCell.Finite) :
    wcd_toVtxFinset unitCell hfin = {((0 : ℤ), (0 : ℤ))} := by
  ext p
  rw [wcd_mem_toVtxFinset]
  simp only [Finset.mem_singleton]
  constructor
  · intro h
    have : (![((0 : ℤ)), 0] : Site 2) = wcd_siteToVtx.symm p := by
      have hu : wcd_siteToVtx.symm p ∈ unitCell := h
      unfold unitCell at hu
      rw [Set.mem_singleton_iff] at hu
      exact hu.symm
    have h0 := congrFun this 0
    have h1 := congrFun this 1
    simp only [wcd_siteToVtx, Equiv.coe_fn_symm_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
    exact Prod.ext h0.symm h1.symm
  · rintro rfl
    show wcd_siteToVtx.symm ((0 : ℤ), (0 : ℤ)) ∈ unitCell
    unfold unitCell
    rw [Set.mem_singleton_iff]
    funext i; fin_cases i <;> rfl







theorem wcd_witness_unitCell :
    cornerBalance unitCell ucBase
      = - ∑ v ∈ regVerts (wcd_toVtxFinset unitCell wcd_unitCell_finite),
          defect (wcd_toVtxFinset unitCell wcd_unitCell_finite) v := by
  rw [unitCell_cornerBalance ucBase (Or.inl rfl), wad_defect_eq_four_chi,
    wcd_toVtxFinset_unitCell, euc_chi_singleton]
  norm_num






theorem wcd_witness_pinch :
    wad_n2d ({((0 : ℤ), (0 : ℤ)), (1, 1)} : Finset (ℤ × ℤ)) = 1 := by decide


theorem wcd_witness_unitSquare_defectSum :
    ∑ v ∈ regVerts ({((0 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)),
        defect ({((0 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)) v = 4 := by
  rw [wad_defect_eq_four_chi, euc_chi_singleton]; norm_num

end Wcd

end StatMech
