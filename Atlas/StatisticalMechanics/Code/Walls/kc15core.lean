/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Code.Walls.kc14core
import Code.Lattice.RotationSystemFaces
import Code.Lattice.FacialSurjectivity
import Code.Lattice.FacialSurjectivityProve

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}
















theorem kc15_facialOrbit_ne_of_component_ne (Vc : (hypercubicLattice 2).Walk a a)
    {s t : Site 2} (hs : s ∉ Vc.support)
    (hne : offSupportComponent Vc s ≠ offSupportComponent Vc t) :
    {e : Dart | IsBoundaryDart (offSupportComponent Vc s) e} ≠
      {e : Dart | IsBoundaryDart (offSupportComponent Vc t) e} := by
  have hdisj := rsf_disjoint_boundaryDarts_of_ne Vc hne
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc hs
  intro heq
  have heU : e ∈ {d : Dart | IsBoundaryDart (offSupportComponent Vc s) d} := he
  have heV : e ∈ {d : Dart | IsBoundaryDart (offSupportComponent Vc t) d} := heq ▸ heU
  exact (Set.disjoint_left.mp hdisj) heU heV




















theorem kc15_beacon_component_infinite (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)).Infinite := by
  set b : Site 2 := ![-((R : ℤ) + 1), 0] with hb
  have hbext : b ∈ exterior 2 R := kc12_farLeftBeacon_mem_exterior R
  have hboff : b ∉ Vc.support := by
    have := oc_exterior_offSupport Vc R hsupp hbext
    simpa [oc_supportSet] using this
  have hbmem : b ∈ (oc_supportSet Vc)ᶜ := kc13_mem_compl Vc hboff
  have hinf := kc4_extComponent_infinite Vc R hsupp hbext hbmem
  intro hfin
  have hfin' : (kc12_component Vc b).Finite := hfin
  exact hinf ((kc13_component_finite_iff Vc hboff hbmem).mpr hfin')


theorem kc15_beacon_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    (![-((R : ℤ) + 1), 0] : Site 2) ∉ Vc.support := by
  have := oc_exterior_offSupport Vc R hsupp (kc12_farLeftBeacon_mem_exterior R)
  simpa [oc_supportSet] using this





theorem kc15_beacon_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    (![-((R : ℤ) + 1), 0] : Site 2) ∉ jec_leftRegion Vc := by
  apply pww_farLeft_notMem_leftRegion
  intro p hp
  have hpbox : p ∈ box 2 R := hsupp (by simpa [oc_supportSet] using hp)
  rw [mem_box] at hpbox
  have h0 := hpbox 0
  change (![-((R : ℤ) + 1), 0] : Site 2) 0 ≤ p 0
  simp only [Matrix.cons_val_zero]
  omega





theorem kc15_finiteComponent_ne_beacon (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hfin : (offSupportComponent Vc z).Finite) :
    offSupportComponent Vc z ≠ offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2) := by
  intro heq
  have hinf := kc15_beacon_component_infinite Vc R hsupp
  rw [heq] at hfin
  exact hinf hfin






theorem kc15_outsideComponent_ne_insideComponent (Vc : (hypercubicLattice 2).Walk a a)
    {z x : Site 2} (hzout : z ∉ jec_leftRegion Vc) (hzoff : z ∉ Vc.support)
    (hxin : x ∈ jec_leftRegion Vc) :
    offSupportComponent Vc z ≠ offSupportComponent Vc x := by
  intro heq
  have hx : x ∈ offSupportComponent Vc x := seed_mem_offSupportComponent Vc x
  rw [← heq] at hx
  exact (offSupportComponent_subset_exterior Vc hzout hzoff hx) hxin










theorem kc15_secondBoundedRegion_third_facialOrbit (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z x : Site 2}
    (hzoff : z ∉ Vc.support) (hzout : z ∉ jec_leftRegion Vc)
    (hfin : (offSupportComponent Vc z).Finite)
    (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support) :
    {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} ≠
      {e : Dart | IsBoundaryDart (offSupportComponent Vc x) e} ∧
    {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} ≠
      {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} ∧
    {e : Dart | IsBoundaryDart (offSupportComponent Vc x) e} ≠
      {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} := by
  refine ⟨?_, ?_, ?_⟩
  · exact kc15_facialOrbit_ne_of_component_ne Vc hzoff
      (kc15_outsideComponent_ne_insideComponent Vc hzout hzoff hxin)
  · exact kc15_facialOrbit_ne_of_component_ne Vc hzoff
      (kc15_finiteComponent_ne_beacon Vc R hsupp hfin)
  · refine kc15_facialOrbit_ne_of_component_ne Vc hxoff ?_
    
    refine fun heq => (kc15_outsideComponent_ne_insideComponent Vc
      (kc15_beacon_outside Vc R hsupp) (kc15_beacon_offSupport Vc R hsupp) hxin) heq.symm


















def kc15_facialFamily (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) (x : Site 2) :
    Set (Set Dart) :=
  {{e : Dart | IsBoundaryDart (offSupportComponent Vc x) e},
   {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e}}







def kc15_FacialOrbitFamilyTwo (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) (x : Site 2) : Prop :=
  rsf_FacialOrbitsCoverComponents Vc (kc15_facialFamily Vc R x)




theorem kc15_facialOrbit_mem_family (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {x z : Site 2}
    (hz : z ∉ Vc.support) (hres : kc15_FacialOrbitFamilyTwo Vc R x) :
    {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} =
        {e : Dart | IsBoundaryDart (offSupportComponent Vc x) e} ∨
      {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} =
        {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} := by
  have hmem : {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e}
      ∈ Set.range (rsf_componentDarts Vc) :=
    ⟨(fcb_offComplGraph Vc).connectedComponentMk ⟨z, hz⟩, rsf_componentDarts_mk Vc ⟨z, hz⟩⟩
  unfold kc15_FacialOrbitFamilyTwo rsf_FacialOrbitsCoverComponents at hres
  rw [hres] at hmem
  simpa only [kc15_facialFamily, Set.mem_insert_iff, Set.mem_singleton_iff] using hmem







theorem kc15_noSecondBoundedRegion_of_facialOrbitFamilyTwo (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R) {x : Site 2}
    (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hres : kc15_FacialOrbitFamilyTwo Vc R x) :
    kc14_NoSecondBoundedRegion Vc := by
  intro z hzoff hzout hfin
  obtain ⟨hzx, hzb, _⟩ :=
    kc15_secondBoundedRegion_third_facialOrbit Vc R hsupp hzoff hzout hfin hxin hxoff
  rcases kc15_facialOrbit_mem_family Vc R hzoff hres with h | h
  · exact hzx h
  · exact hzb h







theorem kc15_offSupportOutsideInfinite_of_facialOrbitFamilyTwo (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hbridge : kc6_OffSupportOutsideInK K a) {x : Site 2}
    (hxin : x ∈ jec_leftRegion (mpl_orbitLoop K a)) (hxoff : x ∉ (mpl_orbitLoop K a).support)
    (hres : kc15_FacialOrbitFamilyTwo (mpl_orbitLoop K a) R x) :
    kc7_OffSupportOutsideInfinite K a :=
  kc14_offSupportOutsideInfinite_of_noSecondBoundedRegion K a R hRbox hbridge
    (kc15_noSecondBoundedRegion_of_facialOrbitFamilyTwo (mpl_orbitLoop K a) R hRbox hxin hxoff hres)
















def kc15_OutsideOneFacialOrbit (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z : Site 2, z ∉ Vc.support → z ∉ jec_leftRegion Vc →
    {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} =
      {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e}






theorem kc15_noSecondBoundedRegion_of_outsideOneFacialOrbit (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hres : kc15_OutsideOneFacialOrbit Vc R) :
    kc14_NoSecondBoundedRegion Vc := by
  intro z hzoff hzout hfin
  have hne : {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e} ≠
      {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e} :=
    kc15_facialOrbit_ne_of_component_ne Vc hzoff (kc15_finiteComponent_ne_beacon Vc R hsupp hfin)
  exact hne (hres z hzoff hzout)







theorem kc15_outsideOneFacialOrbit_of_reachesFarLeftBeacon (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hres : kc12_ReachesFarLeftBeacon Vc R) :
    kc15_OutsideOneFacialOrbit Vc R := by
  intro z hzoff hzout
  obtain ⟨p, hp⟩ := hres z hzoff hzout
  have hr : (offSupport Vc).Reachable z (![-((R : ℤ) + 1), 0] : Site 2) :=
    offSupportWalk_to_offSupport_reachable Vc p hp
  have hcomp : offSupportComponent Vc z
      = offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2) := by
    ext w; rw [mem_offSupportComponent, mem_offSupportComponent]
    exact ⟨fun h => hr.symm.trans h, fun h => hr.trans h⟩
  rw [hcomp]





















theorem kc15_facialOrbitFamilyTwo_of_sides (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {x : Site 2}
    (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ w ∈ p.support, w ∉ Vc.support)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ w ∈ p.support, w ∉ Vc.support) :
    kc15_FacialOrbitFamilyTwo Vc R x := by
  unfold kc15_FacialOrbitFamilyTwo rsf_FacialOrbitsCoverComponents kc15_facialFamily
  rw [fsv_range_eq_canonical]
  exact fsp_canonicalFamily_eq_pair Vc hxin hxoff (kc15_beacon_outside Vc R hsupp)
    (kc15_beacon_offSupport Vc R hsupp) hin hout














theorem kc15_unitCell_outsideOneFacialOrbit :
    kc15_OutsideOneFacialOrbit (mpl_orbitLoop unitCell ucBase) 1 :=
  kc15_outsideOneFacialOrbit_of_reachesFarLeftBeacon (mpl_orbitLoop unitCell ucBase) 1
    kc12_unitCell_reachesFarLeftBeacon






theorem kc15_unitCell_noSecondBoundedRegion_via_facialOrbit :
    kc14_NoSecondBoundedRegion (mpl_orbitLoop unitCell ucBase) :=
  kc15_noSecondBoundedRegion_of_outsideOneFacialOrbit (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc15_unitCell_outsideOneFacialOrbit







theorem kc15_unitCell_finiteComponent_facialOrbit_ne (z : Site 2)
    (hzoff : z ∉ (mpl_orbitLoop unitCell ucBase).support)
    (hfin : (offSupportComponent (mpl_orbitLoop unitCell ucBase) z).Finite) :
    {e : Dart | IsBoundaryDart (offSupportComponent (mpl_orbitLoop unitCell ucBase) z) e} ≠
      {e : Dart | IsBoundaryDart
        (offSupportComponent (mpl_orbitLoop unitCell ucBase) (![-((1 : ℤ) + 1), 0] : Site 2)) e} :=
  kc15_facialOrbit_ne_of_component_ne (mpl_orbitLoop unitCell ucBase) hzoff
    (kc15_finiteComponent_ne_beacon (mpl_orbitLoop unitCell ucBase) 1 kc8_unitCell_supp_box hfin)

end Walls

end StatMech
