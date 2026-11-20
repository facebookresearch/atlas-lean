/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.FloodFillConnected
import Code.Lattice.InsideConnected
import Code.Lattice.StraightWalk
import Code.Lattice.OutsideConnected
import Code.Lattice.OutsideReachesClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}















def ecc_RightStep (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
    ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w



theorem ecc_reach_offSupport (Vc : (hypercubicLattice 2).Walk a a) {z w : Site 2}
    (hzoff : z ∉ Vc.support) (h : (offSupport Vc).Reachable z w) : w ∉ Vc.support := by
  obtain ⟨pw, hpw⟩ := offSupport_reachable_to_offSupportWalk Vc h hzoff
  exact hpw w pw.end_mem_support














theorem ecc_reaches_right_band (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hstep : ecc_RightStep Vc R)
    (z : Site 2) (hzout : z ∉ jec_leftRegion Vc) (hzoff : z ∉ Vc.support) :
    ∃ w : Site 2, (R : ℤ) + 1 ≤ w 0 ∧ (offSupport Vc).Reachable z w := by
  generalize hm : ((R : ℤ) + 1 - z 0).toNat = m
  induction m using Nat.strong_induction_on generalizing z with
  | _ m ih =>
    rcases le_or_gt ((R : ℤ) + 1) (z 0) with hge | hlt
    · exact ⟨z, hge, SimpleGraph.Reachable.refl _⟩
    · have hzR : z 0 ≤ (R : ℤ) := by omega
      obtain ⟨w, hprog, hreach⟩ := hstep z hzout hzoff hzR
      have hwoff : w ∉ Vc.support := ecc_reach_offSupport Vc hzoff hreach
      have hwout : w ∉ jec_leftRegion Vc :=
        offSupport_component_monochromatic_out Vc hzout hreach hzoff
      have hmw : ((R : ℤ) + 1 - w 0).toNat < m := by rw [← hm]; omega
      obtain ⟨u, hu, hwu⟩ := ih _ hmw w hwout hwoff rfl
      exact ⟨u, hu, hreach.trans hwu⟩














theorem ecc_outsideReachesExterior_of_rightStep (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
    (hstep : ecc_RightStep Vc R) :
    oc_OutsideReachesExterior Vc R := by
  intro z hz
  have hzoff : z ∉ Vc.support := hoffOut z hz
  obtain ⟨w, hw, hreach⟩ := ecc_reaches_right_band Vc R hstep z hz hzoff
  have hwExt : w ∈ exterior 2 R := oc_mem_exterior_of_col_high R hw
  exact ⟨w, hwExt, orc_offSupportLattice_reachable_of_offSupport Vc hzoff hreach⟩











theorem ecc_exteriorCovered_of_rightStep (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
    {beacon : Site 2} (hbExt : beacon ∈ exterior 2 R)
    (hstep : ecc_RightStep Vc R) :
    orc_ExteriorCovered Vc beacon :=
  orc_exteriorCovered_of_outsideReachesExterior Vc R hsupp hbExt
    (ecc_outsideReachesExterior_of_rightStep Vc R hoffOut hstep)











theorem ecc_two_components_of_rightStep (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
    (hstep : ecc_RightStep Vc R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  oc_two_components_of_outsideReaches Vc R hsupp hp hq hInOff
    (ecc_outsideReachesExterior_of_rightStep Vc R hoffOut hstep)










theorem ecc_rightNeighbor_step (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hzoff : z ∉ Vc.support) (hnbOff : (![z 0 + 1, z 1] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z ![z 0 + 1, z 1] := by
  have hadj : (hypercubicLattice 2).Adj z ![z 0 + 1, z 1] := by
    have h := sw_adj_horizSucc (z 1) (z 0)
    have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
    rw [hzeq]; exact h
  exact (Adj.reachable ⟨hadj, hzoff, hnbOff⟩ : (offSupport Vc).Reachable _ _)



def ecc_RightDodge (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
    (![z 0 + 1, z 1] : Site 2) ∈ Vc.support →
    ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w




theorem ecc_rightStep_of_rightDodge (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hdodge : ecc_RightDodge Vc R) : ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  by_cases hnb : (![z 0 + 1, z 1] : Site 2) ∈ Vc.support
  · exact hdodge z hzout hzoff hzR hnb
  · exact ⟨![z 0 + 1, z 1], by simp, ecc_rightNeighbor_step Vc hzoff hnb⟩











theorem ecc_rightStep_of_rightNeighbor_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hnb : ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
        (![z 0 + 1, z 1] : Site 2) ∉ Vc.support) :
    ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  exact ⟨![z 0 + 1, z 1], by simp,
    ecc_rightNeighbor_step Vc hzoff (hnb z hzout hzoff hzR)⟩










theorem ecc_rightStep_of_floodFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hflood : oc_OutsideReachesExterior Vc R) :
    ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  obtain ⟨e, heExt, hreach⟩ := hflood z hzout
  
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







theorem ecc_rightStep_iff_exteriorCovered (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
    {beacon : Site 2} (hbExt : beacon ∈ exterior 2 R) (hbOff : beacon ∉ Vc.support) :
    ecc_RightStep Vc R ↔ orc_ExteriorCovered Vc beacon := by
  constructor
  · intro hstep
    exact ecc_exteriorCovered_of_rightStep Vc R hsupp hoffOut hbExt hstep
  · intro hcov
    exact ecc_rightStep_of_floodFill Vc R hsupp
      (orc_outsideReachesExterior_of_exteriorCovered Vc R hbExt hbOff hcov)

end Lattice

end StatMech
