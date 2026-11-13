/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Lattice.InsideConnected
import Code.Lattice.FaceComponentBijection
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.OutsideConnected
import Code.Lattice.EulerGeometricFaces
import Code.Walls.wpjplanarjordan
import Code.Walls.wocoutsidetop

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}












theorem wch_bridge_false (Vc : (hypercubicLattice 2).Walk a a) :
    ¬ wpj_PlaneDualityBridge Vc := by
  rintro ⟨hoffIn, hoffOut, -, -, -, -⟩
  have ha : a ∈ Vc.support := Vc.start_mem_support
  by_cases h : a ∈ jec_leftRegion Vc
  · exact hoffIn a h ha
  · exact hoffOut a h ha







theorem wch_covers_off_pair_false (Vc : (hypercubicLattice 2).Walk a a)
    {sIn sOut : Site 2} (hsInoff : sIn ∉ Vc.support) (hsOutoff : sOut ∉ Vc.support)
    (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn)
    (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) : False := by
  have ha : a ∈ Vc.support := Vc.start_mem_support
  by_cases h : a ∈ jec_leftRegion Vc
  · exact offSupportComponent_offSupport Vc hsInoff (hcovIn h) ha
  · exact offSupportComponent_offSupport Vc hsOutoff (hcovOut h) ha









def wch_InteriorCovering (Vc : (hypercubicLattice 2).Walk a a) (sIn : Site 2) : Prop :=
  ∀ z : Site 2, z ∈ jec_leftRegion Vc → z ∉ Vc.support → z ∈ offSupportComponent Vc sIn



def wch_ExteriorCovering (Vc : (hypercubicLattice 2).Walk a a) (sOut : Site 2) : Prop :=
  ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z ∈ offSupportComponent Vc sOut




def wch_CorrectedBridge (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  (∃ sIn, sIn ∈ jec_leftRegion Vc ∧ sIn ∉ Vc.support ∧ wch_InteriorCovering Vc sIn) ∧
    (∃ sOut, sOut ∉ jec_leftRegion Vc ∧ sOut ∉ Vc.support ∧ wch_ExteriorCovering Vc sOut)






theorem wch_offComplJordanRegion_of_corrected (Vc : (hypercubicLattice 2).Walk a a)
    (h : wch_CorrectedBridge Vc) : fcb_OffComplJordanRegion Vc := by
  obtain ⟨⟨sIn, hsInmem, hsInoff, hcovIn⟩, ⟨sOut, hsOutmem, hsOutoff, hcovOut⟩⟩ := h
  refine ⟨⟨sIn, hsInmem, hsInoff⟩, ⟨sOut, hsOutmem, hsOutoff⟩, ?_, ?_⟩
  · 
    intro s t hs ht hsoff htoff
    have hsc : (offSupport Vc).Reachable sIn s :=
      (mem_offSupportComponent Vc).mp (hcovIn s hs hsoff)
    have htc : (offSupport Vc).Reachable sIn t :=
      (mem_offSupportComponent Vc).mp (hcovIn t ht htoff)
    exact offSupport_reachable_to_offSupportWalk Vc (hsc.symm.trans htc) hsoff
  · 
    intro s t hs ht hsoff htoff
    have hsc : (offSupport Vc).Reachable sOut s :=
      (mem_offSupportComponent Vc).mp (hcovOut s hs hsoff)
    have htc : (offSupport Vc).Reachable sOut t :=
      (mem_offSupportComponent Vc).mp (hcovOut t ht htoff)
    exact offSupport_reachable_to_offSupportWalk Vc (hsc.symm.trans htc) hsoff





theorem wch_winding_separation_of_corrected (Vc : (hypercubicLattice 2).Walk a a)
    (h : wch_CorrectedBridge Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 :=
  fcb_two_components_of_region Vc (wch_offComplJordanRegion_of_corrected Vc h)
















theorem wch_exteriorCovering_of_noBoundedEven (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : woc_NoBoundedEvenComponent Vc) :
    (beacon 2 R) ∉ jec_leftRegion Vc ∧ (beacon 2 R) ∉ Vc.support ∧
      wch_ExteriorCovering Vc (beacon 2 R) := by
  have hbext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  refine ⟨oc_exterior_outside Vc R (fun p hp => hsupp hp) hbext,
    oc_exterior_offSupport Vc R hsupp hbext, ?_⟩
  intro z hzout hzoff
  
  have hinf : (offSupportComponent Vc z).Infinite := fun hfin => hzout (h z hzoff hfin)
  obtain ⟨e, he, hze⟩ := woc_infinite_reachesExterior Vc R hzoff hinf
  
  have hbe : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable (beacon 2 R) e :=
    oc_exterior_reachable_offSupport Vc R hsupp hbext he
  have hbz : (offSupport Vc).Reachable (beacon 2 R) z :=
    (woc_reachable_iff Vc).mpr (hbe.trans hze.symm)
  exact (mem_offSupportComponent Vc).mpr hbz










def wch_InteriorConnected (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∃ sIn, sIn ∈ jec_leftRegion Vc ∧ sIn ∉ Vc.support ∧ wch_InteriorCovering Vc sIn








theorem wch_winding_separation_of_residues (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hIntConn : wch_InteriorConnected Vc)
    (hNoBddEven : woc_NoBoundedEvenComponent Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
  refine wch_winding_separation_of_corrected Vc ⟨hIntConn, ?_⟩
  obtain ⟨h1, h2, h3⟩ := wch_exteriorCovering_of_noBoundedEven Vc R hsupp hNoBddEven
  exact ⟨beacon 2 R, h1, h2, h3⟩












theorem wch_interiorConnected_iff (Vc : (hypercubicLattice 2).Walk a a)
    {sIn : Site 2} (hsInmem : sIn ∈ jec_leftRegion Vc) (hsInoff : sIn ∉ Vc.support) :
    wch_InteriorConnected Vc ↔
      ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support → (offSupport Vc).Reachable s t := by
  constructor
  · rintro ⟨seed, _, hseedoff, hcov⟩ s t hs ht hsoff htoff
    have hsc : (offSupport Vc).Reachable seed s := (mem_offSupportComponent Vc).mp (hcov s hs hsoff)
    have htc : (offSupport Vc).Reachable seed t := (mem_offSupportComponent Vc).mp (hcov t ht htoff)
    exact hsc.symm.trans htc
  · intro hconn
    refine ⟨sIn, hsInmem, hsInoff, ?_⟩
    intro z hz hzoff
    exact (mem_offSupportComponent Vc).mpr (hconn sIn z hsInmem hz hsInoff hzoff)

end Lattice

end StatMech
