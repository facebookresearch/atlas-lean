/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Code.Walls.kc12core

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}











def kc13_NoFiniteHole (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ z : Site 2, z ∉ Vc.support → z ∉ jec_leftRegion Vc →
    ∀ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
      ¬ (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Finite


theorem kc13_mem_compl (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) : z ∈ (oc_supportSet Vc)ᶜ := by
  simpa [oc_supportSet] using hz






theorem kc13_reachesFarLeftBeacon_of_noFiniteHole (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (hres : kc13_NoFiniteHole Vc) :
    kc12_ReachesFarLeftBeacon Vc R := by
  refine kc12_reachesFarLeftBeacon_of_offSupportReaches Vc R hsupp ?_
  intro z hzoff hzout
  have hzmem : z ∈ (oc_supportSet Vc)ᶜ := kc13_mem_compl Vc hzoff
  have hnotfin := hres z hzoff hzout hzmem
  have hinf : (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
      ⟨z, hzmem⟩).supp.Infinite := hnotfin
  exact kc4_reaches_exterior_of_infiniteComponent Vc R hsupp hzmem hinf






theorem kc13_noFiniteHole_of_reachesFarLeftBeacon (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (hres : kc12_ReachesFarLeftBeacon Vc R) :
    kc13_NoFiniteHole Vc := by
  classical
  intro z hzoff hzout hzmem hfin
  
  obtain ⟨p, hp⟩ := hres z hzoff hzout
  
  have hbmem : (![-((R : ℤ) + 1), 0] : Site 2) ∈ (oc_supportSet Vc)ᶜ := by
    have := hp _ p.end_mem_support
    simpa [oc_supportSet] using this
  
  have hindReach :
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).Reachable ⟨z, hzmem⟩ ⟨_, hbmem⟩ :=
    walk_induce_reachable (hypercubicLattice 2) ((oc_supportSet Vc)ᶜ) p
      (fun w hw => by simpa [oc_supportSet] using hp w hw) hzmem hbmem
  
  have hcompEq :
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩ =
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨_, hbmem⟩ :=
    ConnectedComponent.sound hindReach
  
  have hbext : (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := kc12_farLeftBeacon_mem_exterior R
  have hinf :
      (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨_, hbmem⟩).supp.Infinite :=
    kc4_extComponent_infinite Vc R hsupp hbext hbmem
  rw [hcompEq] at hfin
  exact hinf hfin







theorem kc13_reachesFarLeftBeacon_iff_noFiniteHole (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    kc12_ReachesFarLeftBeacon Vc R ↔ kc13_NoFiniteHole Vc :=
  ⟨kc13_noFiniteHole_of_reachesFarLeftBeacon Vc R hsupp,
   kc13_reachesFarLeftBeacon_of_noFiniteHole Vc R hsupp⟩














theorem kc13_offSupport_reachable_iff_induce (Vc : (hypercubicLattice 2).Walk a a) {z y : Site 2}
    (hz : z ∈ (oc_supportSet Vc)ᶜ) (hy : y ∈ (oc_supportSet Vc)ᶜ) :
    (offSupport Vc).Reachable z y ↔
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).Reachable ⟨z, hz⟩ ⟨y, hy⟩ := by
  have hzoff : z ∉ Vc.support := by simpa [oc_supportSet] using hz
  constructor
  · intro h
    obtain ⟨p, hp⟩ := offSupport_reachable_to_offSupportWalk Vc h hzoff
    exact walk_induce_reachable (hypercubicLattice 2) ((oc_supportSet Vc)ᶜ) p
      (fun w hw => by simpa [oc_supportSet] using hp w hw) hz hy
  · intro h
    
    obtain ⟨pw, hpw⟩ := exc_reachable_compl_to_offSupport_walk (oc_supportSet Vc) hz hy h
    exact offSupportWalk_to_offSupport_reachable Vc pw
      (fun w hw => by simpa [oc_supportSet] using hpw w hw)





theorem kc13_component_finite_iff (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hzmem : z ∈ (oc_supportSet Vc)ᶜ) :
    (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
      ⟨z, hzmem⟩).supp.Finite ↔ (kc12_component Vc z).Finite := by
  classical
  set G := (hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ with hG
  
  have himage :
      Subtype.val '' (G.connectedComponentMk ⟨z, hzmem⟩).supp = kc12_component Vc z := by
    ext y
    simp only [Set.mem_image, ConnectedComponent.mem_supp_iff]
    constructor
    · rintro ⟨⟨w, hw⟩, hwc, rfl⟩
      have hreach : G.Reachable ⟨z, hzmem⟩ ⟨w, hw⟩ := ConnectedComponent.eq.mp hwc.symm
      exact (kc13_offSupport_reachable_iff_induce Vc hzmem hw).mpr hreach
    · intro hy
      have hyoff : y ∉ Vc.support := kc12_offSupport_reachable_offSupport Vc hz hy
      have hymem : y ∈ (oc_supportSet Vc)ᶜ := by simpa [oc_supportSet] using hyoff
      refine ⟨⟨y, hymem⟩, ?_, rfl⟩
      refine (ConnectedComponent.eq.mpr ?_).symm
      exact (kc13_offSupport_reachable_iff_induce Vc hzmem hymem).mp hy
  constructor
  · intro hfin
    rw [← himage]; exact hfin.image _
  · intro hfin
    have : (Subtype.val '' (G.connectedComponentMk ⟨z, hzmem⟩).supp).Finite := himage ▸ hfin
    exact this.of_finite_image (Set.injOn_of_injective Subtype.val_injective)















theorem kc13_neighbour_in_component_or_onSupport (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) {w w' : Site 2} (hwC : w ∈ kc12_component Vc z)
    (hadj : (hypercubicLattice 2).Adj w w') :
    w' ∈ kc12_component Vc z ∨ w' ∈ Vc.support := by
  rw [or_iff_not_imp_right]
  intro hw'off
  have hwreach : (offSupport Vc).Reachable z w := hwC
  have hwoff : w ∉ Vc.support := kc12_offSupport_reachable_offSupport Vc hz hwreach
  have hoffadj : (offSupport Vc).Adj w w' := (offSupport_adj Vc w w').mpr ⟨hadj, hwoff, hw'off⟩
  exact hwreach.trans hoffadj.reachable







theorem kc13_finiteComponent_boundary_onSupport (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) {w w' : Site 2} (hwC : w ∈ kc12_component Vc z)
    (hadj : (hypercubicLattice 2).Adj w w') (hw'notC : w' ∉ kc12_component Vc z) :
    w' ∈ Vc.support :=
  (kc13_neighbour_in_component_or_onSupport Vc hz hwC hadj).resolve_left hw'notC













theorem kc13_finiteComponent_outside (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hzout : z ∉ jec_leftRegion Vc) {w : Site 2}
    (hwC : w ∈ kc12_component Vc z) : w ∉ jec_leftRegion Vc :=
  offSupport_component_monochromatic_out Vc hzout hwC hz








theorem kc13_target_fails_iff_finite_evenComponent (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    ¬ kc12_ReachesFarLeftBeacon Vc R ↔
      ∃ z : Site 2, z ∉ Vc.support ∧ z ∉ jec_leftRegion Vc ∧ (kc12_component Vc z).Finite := by
  rw [kc13_reachesFarLeftBeacon_iff_noFiniteHole Vc R hsupp]
  constructor
  · intro hnot
    rw [kc13_NoFiniteHole] at hnot
    push Not at hnot
    obtain ⟨z, hzoff, hzout, hzmem, hfin⟩ := hnot
    refine ⟨z, hzoff, hzout, ?_⟩
    rw [← kc13_component_finite_iff Vc hzoff hzmem]
    exact not_not.mp (by simpa using hfin)
  · rintro ⟨z, hzoff, hzout, hfin⟩
    intro hres
    have hzmem : z ∈ (oc_supportSet Vc)ᶜ := kc13_mem_compl Vc hzoff
    have hnotfin := hres z hzoff hzout hzmem
    exact hnotfin ((kc13_component_finite_iff Vc hzoff hzmem).mpr hfin)





theorem kc13_offSupportOutsideInfinite_of_noFiniteHole (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hbridge : kc6_OffSupportOutsideInK K a)
    (hres : kc13_NoFiniteHole (mpl_orbitLoop K a)) :
    kc7_OffSupportOutsideInfinite K a :=
  kc12_offSupportOutsideInfinite_of_reachesFarLeft K a R hRbox hbridge
    (kc13_reachesFarLeftBeacon_of_noFiniteHole (mpl_orbitLoop K a) R hRbox hres)





theorem kc13_unitCell_noFiniteHole :
    kc13_NoFiniteHole (mpl_orbitLoop unitCell ucBase) :=
  kc13_noFiniteHole_of_reachesFarLeftBeacon (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc12_unitCell_reachesFarLeftBeacon


theorem kc13_unitCell_reachesFarLeftBeacon :
    kc12_ReachesFarLeftBeacon (mpl_orbitLoop unitCell ucBase) 1 :=
  kc13_reachesFarLeftBeacon_of_noFiniteHole (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc13_unitCell_noFiniteHole

end Walls

end StatMech
