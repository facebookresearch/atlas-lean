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

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}















theorem orc_offSupportLattice_reachable_of_offSupport (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∉ Vc.support) (h : (offSupport Vc).Reachable x y) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
  obtain ⟨p, hp⟩ := offSupport_reachable_to_offSupportWalk Vc h hx
  exact (oc_offSupportLattice_reachable_iff Vc hx).mpr ⟨p, hp⟩




theorem orc_offSupport_reachable_of_offSupportLattice (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∉ Vc.support)
    (h : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y) :
    (offSupport Vc).Reachable x y := by
  obtain ⟨p, hp⟩ := (oc_offSupportLattice_reachable_iff Vc hx).mp h
  exact offSupportWalk_to_offSupport_reachable Vc p hp


















def orc_ExteriorCovered (Vc : (hypercubicLattice 2).Walk a a) (beacon : Site 2) : Prop :=
  (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc beacon



theorem orc_exteriorHub_of_covered (Vc : (hypercubicLattice 2).Walk a a) {beacon : Site 2}
    (hcov : orc_ExteriorCovered Vc beacon) :
    ∀ s : Site 2, s ∉ jec_leftRegion Vc → (offSupport Vc).Reachable beacon s :=
  fun _ hs => (mem_offSupportComponent Vc).mp (hcov hs)

















theorem orc_outsideReachesExterior_of_exteriorCovered (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) {beacon : Site 2} (hbExt : beacon ∈ exterior 2 R) (hbOff : beacon ∉ Vc.support)
    (hcov : orc_ExteriorCovered Vc beacon) :
    oc_OutsideReachesExterior Vc R := by
  intro z hz
  
  have hbz : (offSupport Vc).Reachable beacon z := orc_exteriorHub_of_covered Vc hcov z hz
  
  have hzoff : z ∉ Vc.support :=
    offSupportComponent_offSupport Vc hbOff (hcov hz)
  
  have hzb : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z beacon :=
    orc_offSupportLattice_reachable_of_offSupport Vc hzoff hbz.symm
  exact ⟨beacon, hbExt, hzb⟩

















theorem orc_exteriorCovered_of_outsideReachesExterior (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {beacon : Site 2} (hbExt : beacon ∈ exterior 2 R)
    (hFlood : oc_OutsideReachesExterior Vc R) :
    orc_ExteriorCovered Vc beacon := by
  intro z hz
  rw [mem_offSupportComponent]
  
  obtain ⟨ez, hezExt, hreach_z⟩ := hFlood z (by simpa using hz)
  
  have hzoff : z ∉ Vc.support := by
    rcases hreach_z with ⟨w⟩
    cases w with
    | nil => exact oc_exterior_offSupport Vc R hsupp hezExt
    | cons hadj _ => exact hadj.2.1
  
  have hmid : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable ez beacon :=
    oc_exterior_reachable_offSupport Vc R hsupp hezExt hbExt
  
  have hzb : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z beacon := hreach_z.trans hmid
  exact (orc_offSupport_reachable_of_offSupportLattice Vc hzoff hzb).symm






theorem orc_exteriorCovered_iff_outsideReachesExterior (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {beacon : Site 2} (hbExt : beacon ∈ exterior 2 R) (hbOff : beacon ∉ Vc.support) :
    orc_ExteriorCovered Vc beacon ↔ oc_OutsideReachesExterior Vc R :=
  ⟨orc_outsideReachesExterior_of_exteriorCovered Vc R hbExt hbOff,
    orc_exteriorCovered_of_outsideReachesExterior Vc R hsupp hbExt⟩


















theorem orc_reachesExterior_of_anyClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear :
      (∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support)) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  rcases hclear with h | h | h | h
  · exact oc_reachesExterior_of_vertUpClear Vc R h
  · exact oc_reachesExterior_of_vertDownClear Vc R h
  · exact oc_reachesExterior_of_horizRightClear Vc R h
  · exact oc_reachesExterior_of_horizLeftClear Vc R h








theorem orc_anyClear_inhabits_conclusion (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear :
      (∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support)) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e :=
  orc_reachesExterior_of_anyClear Vc R hclear
















theorem orc_exteriorCovered_of_outside_eq_exterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {beacon : Site 2} (hbExt : beacon ∈ exterior 2 R) (hbOff : beacon ∉ Vc.support)
    (hout : (jec_leftRegion Vc)ᶜ ⊆ exterior 2 R) :
    orc_ExteriorCovered Vc beacon := by
  intro z hz
  rw [mem_offSupportComponent]
  have hzExt : z ∈ exterior 2 R := hout hz
  have hzoff : z ∉ Vc.support := oc_exterior_offSupport Vc R hsupp hzExt
  
  have hbz : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable beacon z :=
    oc_exterior_reachable_offSupport Vc R hsupp hbExt hzExt
  exact orc_offSupport_reachable_of_offSupportLattice Vc hbOff hbz












theorem orc_hOutOff_of_exteriorCovered (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {beacon : Site 2} (hbExt : beacon ∈ exterior 2 R) (hbOff : beacon ∉ Vc.support)
    (hcov : orc_ExteriorCovered Vc beacon) :
    ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
      ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support :=
  oc_hOutOff_of_reachesExterior Vc R hsupp
    (orc_outsideReachesExterior_of_exteriorCovered Vc R hbExt hbOff hcov)












theorem orc_two_components_of_exteriorCovered (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    {beacon : Site 2} (hbExt : beacon ∈ exterior 2 R) (hbOff : beacon ∉ Vc.support)
    (hcov : orc_ExteriorCovered Vc beacon) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  oc_two_components_of_outsideReaches Vc R hsupp hp hq hInOff
    (orc_outsideReachesExterior_of_exteriorCovered Vc R hbExt hbOff hcov)

end Lattice

end StatMech
