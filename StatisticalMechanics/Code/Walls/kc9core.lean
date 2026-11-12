/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































































import Code.Walls.kc8core
import Code.Lattice.ExteriorCoveredClose

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


























theorem kc9_offSupportReaches_of_rightStep (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hstep : ecc_RightStep Vc R) :
    kc5_OffSupportReachesExterior Vc R := by
  intro z hzoff hzout
  obtain ⟨w, hw, hreach⟩ := ecc_reaches_right_band Vc R hstep z hzout hzoff
  exact ⟨w, oc_mem_exterior_of_col_high R hw,
    orc_offSupportLattice_reachable_of_offSupport Vc hzoff hreach⟩










theorem kc9_offSupportReaches_of_rightDodge (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hdodge : ecc_RightDodge Vc R) :
    kc5_OffSupportReachesExterior Vc R :=
  kc9_offSupportReaches_of_rightStep Vc R (ecc_rightStep_of_rightDodge Vc R hdodge)













theorem kc9_outsideOffSupportInfinite_of_rightDodge (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (hdodge : ecc_RightDodge Vc R) :
    kc5_OutsideOffSupportInfinite Vc :=
  kc8_outsideOffSupportInfinite_of_offSupportReaches Vc R hsupp
    (kc9_offSupportReaches_of_rightDodge Vc R hdodge)











theorem kc9_offSupportOutsideInfinite_of_rightDodge (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hbridge : kc6_OffSupportOutsideInK K a)
    (hdodge : ecc_RightDodge (mpl_orbitLoop K a) R) :
    kc7_OffSupportOutsideInfinite K a :=
  kc8_offSupportOutsideInfinite_of_offSupportReaches K a R hRbox hbridge
    (kc9_offSupportReaches_of_rightDodge (mpl_orbitLoop K a) R hdodge)












theorem kc9_upStep (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hzoff : z ∉ Vc.support) (hupOff : (![z 0, z 1 + 1] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z ![z 0, z 1 + 1] := by
  have hadj : (hypercubicLattice 2).Adj z ![z 0, z 1 + 1] := by
    have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
    rw [hzeq]; exact sw_adj_vertSucc (z 0) (z 1)
  exact (Adj.reachable ⟨hadj, hzoff, hupOff⟩ : (offSupport Vc).Reachable _ _)




theorem kc9_downStep (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hzoff : z ∉ Vc.support) (hdownOff : (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z ![z 0, z 1 - 1] := by
  have hadj : (hypercubicLattice 2).Adj z ![z 0, z 1 - 1] := by
    have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
    have h := sw_adj_vertSucc (z 0) (z 1 - 1)
    rw [show z 1 - 1 + 1 = z 1 by ring] at h
    rw [hzeq]; exact h.symm
  exact (Adj.reachable ⟨hadj, hzoff, hdownOff⟩ : (offSupport Vc).Reachable _ _)





theorem kc9_overTop_dodge (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hzoff : z ∉ Vc.support)
    (hupOff : (![z 0, z 1 + 1] : Site 2) ∉ Vc.support)
    (hupRightOff : (![z 0 + 1, z 1 + 1] : Site 2) ∉ Vc.support) :
    ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w := by
  have step1 : (offSupport Vc).Reachable z ![z 0, z 1 + 1] := kc9_upStep Vc hzoff hupOff
  have hadj2 : (hypercubicLattice 2).Adj (![z 0, z 1 + 1] : Site 2) ![z 0 + 1, z 1 + 1] :=
    sw_adj_horizSucc (z 1 + 1) (z 0)
  have step2 : (offSupport Vc).Reachable (![z 0, z 1 + 1] : Site 2) ![z 0 + 1, z 1 + 1] :=
    (Adj.reachable ⟨hadj2, hupOff, hupRightOff⟩ : (offSupport Vc).Reachable _ _)
  exact ⟨![z 0 + 1, z 1 + 1], by simp, step1.trans step2⟩





theorem kc9_underBottom_dodge (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hzoff : z ∉ Vc.support)
    (hdownOff : (![z 0, z 1 - 1] : Site 2) ∉ Vc.support)
    (hdownRightOff : (![z 0 + 1, z 1 - 1] : Site 2) ∉ Vc.support) :
    ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w := by
  have step1 : (offSupport Vc).Reachable z ![z 0, z 1 - 1] := kc9_downStep Vc hzoff hdownOff
  have hadj2 : (hypercubicLattice 2).Adj (![z 0, z 1 - 1] : Site 2) ![z 0 + 1, z 1 - 1] :=
    sw_adj_horizSucc (z 1 - 1) (z 0)
  have step2 : (offSupport Vc).Reachable (![z 0, z 1 - 1] : Site 2) ![z 0 + 1, z 1 - 1] :=
    (Adj.reachable ⟨hadj2, hdownOff, hdownRightOff⟩ : (offSupport Vc).Reachable _ _)
  exact ⟨![z 0 + 1, z 1 - 1], by simp, step1.trans step2⟩










theorem kc9_rightStep_of_localDodge (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hloc : ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
      (![z 0 + 1, z 1] : Site 2) ∉ Vc.support ∨
      ((![z 0, z 1 + 1] : Site 2) ∉ Vc.support ∧ (![z 0 + 1, z 1 + 1] : Site 2) ∉ Vc.support) ∨
      ((![z 0, z 1 - 1] : Site 2) ∉ Vc.support ∧ (![z 0 + 1, z 1 - 1] : Site 2) ∉ Vc.support)) :
    ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  rcases hloc z hzout hzoff hzR with hnb | ⟨hu, hur⟩ | ⟨hd, hdr⟩
  · exact ⟨![z 0 + 1, z 1], by simp, ecc_rightNeighbor_step Vc hzoff hnb⟩
  · exact kc9_overTop_dodge Vc hzoff hu hur
  · exact kc9_underBottom_dodge Vc hzoff hd hdr





theorem kc9_offSupportReaches_of_localDodge (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hloc : ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
      (![z 0 + 1, z 1] : Site 2) ∉ Vc.support ∨
      ((![z 0, z 1 + 1] : Site 2) ∉ Vc.support ∧ (![z 0 + 1, z 1 + 1] : Site 2) ∉ Vc.support) ∨
      ((![z 0, z 1 - 1] : Site 2) ∉ Vc.support ∧ (![z 0 + 1, z 1 - 1] : Site 2) ∉ Vc.support)) :
    kc5_OffSupportReachesExterior Vc R :=
  kc9_offSupportReaches_of_rightStep Vc R (kc9_rightStep_of_localDodge Vc R hloc)














theorem kc9_rightStep_of_offSupportReaches (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hesc : kc5_OffSupportReachesExterior Vc R) :
    ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  obtain ⟨e, heExt, hreach⟩ := hesc z hzoff hzout
  set u : Site 2 := ![(R : ℤ) + 1 + max (z 0) 0, z 1] with hu
  have huExt : u ∈ exterior 2 R := by
    refine oc_mem_exterior_of_col_high R ?_
    rw [hu]; simp only [Matrix.cons_val_zero]
    have : (0 : ℤ) ≤ max (z 0) 0 := le_max_right _ _
    omega
  have hprog : z 0 < u 0 := by
    rw [hu]; simp only [Matrix.cons_val_zero]
    have h1 : z 0 ≤ max (z 0) 0 := le_max_left _ _
    have hR : (0 : ℤ) ≤ (R : ℤ) := by positivity
    omega
  have hmid : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable e u :=
    oc_exterior_reachable_offSupport Vc R hsupp heExt huExt
  have hzu_ffc : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z u := hreach.trans hmid
  exact ⟨u, hprog, orc_offSupport_reachable_of_offSupportLattice Vc hzoff hzu_ffc⟩







theorem kc9_rightDodge_of_offSupportReaches (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hesc : kc5_OffSupportReachesExterior Vc R) :
    ecc_RightDodge Vc R := by
  intro z hzout hzoff hzR _
  exact kc9_rightStep_of_offSupportReaches Vc R hsupp hesc z hzout hzoff hzR







theorem kc9_offSupportReaches_iff_rightStep (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    kc5_OffSupportReachesExterior Vc R ↔ ecc_RightStep Vc R :=
  ⟨kc9_rightStep_of_offSupportReaches Vc R hsupp, kc9_offSupportReaches_of_rightStep Vc R⟩













theorem kc9_unitCell_rightDodge :
    ecc_RightDodge (mpl_orbitLoop unitCell ucBase) 1 :=
  kc9_rightDodge_of_offSupportReaches (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc8_unitCell_offSupportReaches







theorem kc9_unitCell_offSupportReaches_via_dodge :
    kc5_OffSupportReachesExterior (mpl_orbitLoop unitCell ucBase) 1 :=
  kc9_offSupportReaches_of_rightDodge (mpl_orbitLoop unitCell ucBase) 1 kc9_unitCell_rightDodge






theorem kc9_unitCell_outsideOffSupportInfinite_via_dodge :
    kc5_OutsideOffSupportInfinite (mpl_orbitLoop unitCell ucBase) :=
  kc9_outsideOffSupportInfinite_of_rightDodge (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc9_unitCell_rightDodge













































end Walls

end StatMech
