/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































































import Code.Walls.kc5_core
import Code.Walls.kc6evenoddrule
import Code.Walls.kc6uniqueinfinitecomponent
import Code.Walls.kc6cornercellodd
import Code.Walls.kc6windingwitness
import Code.Walls.kc3_core
import Code.Walls.kc3_oddrayeqleftRegion
import Code.Lattice.WindingWitnessClose

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice


















theorem kc6_interiorSubset_of_halves (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a)
    (hsupp : exc_SupportOddInK K a) :
    eaw_InteriorSubset K a :=
  exc_interiorSubset_of_reaches_and_support K a hoff hsupp





theorem kc6_leftRegion_subset_of_halves (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a)
    (hsupp : exc_SupportOddInK K a) :
    jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
  intro z hz
  rw [jec_mem_leftRegion] at hz
  exact kc6_interiorSubset_of_halves K a hoff hsupp z hz





















def kc6_OffSupportOutsideInK (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z, z ∉ K → z ∉ (mpl_orbitLoop K a).support → z ∉ jec_leftRegion (mpl_orbitLoop K a)












theorem kc6_offSupportReaches_of_noHoles (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hbridge : kc6_OffSupportOutsideInK K a)
    (hnoHoles : kc5_OutsideOffSupportInfinite (mpl_orbitLoop K a)) :
    exc_OffSupportReachesExterior K a := by
  refine ⟨R, hRbox, ?_⟩
  intro z hzK hzsupp
  
  have hzOut : z ∉ jec_leftRegion (mpl_orbitLoop K a) := hbridge z hzK hzsupp
  
  obtain ⟨hzmem, hinf⟩ := hnoHoles z hzsupp hzOut
  
  have hsuppbox : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R := fun _ hp => hRbox hp
  
  obtain ⟨e, heExt, hreach⟩ :=
    kc4_reaches_exterior_of_infiniteComponent (mpl_orbitLoop K a) R hsuppbox hzmem hinf
  
  
  have hzB : z ∉ ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) := hzmem
  obtain ⟨hemem, hreach'⟩ := kc3_inducedReachable_of_floodFill (mpl_orbitLoop K a) hzB hreach
  exact ⟨hzmem, e, heExt, hreach'⟩


























theorem kc6_interiorSubset_of_supportOdd_and_bridge (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hsupp : exc_SupportOddInK K a)
    (hbridge : kc6_OffSupportOutsideInK K a) :
    eaw_InteriorSubset K a := by
  intro z hodd
  by_cases hzsupp : z ∈ (mpl_orbitLoop K a).support
  · exact hsupp z hzsupp hodd
  · by_contra hzK
    have hout : z ∉ jec_leftRegion (mpl_orbitLoop K a) := hbridge z hzK hzsupp
    rw [jec_mem_leftRegion] at hout
    exact hout hodd





theorem kc6_bridge_iff_offSupport_inside_subset (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    kc6_OffSupportOutsideInK K a ↔
      ∀ z, z ∉ (mpl_orbitLoop K a).support →
        ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) → z ∈ K := by
  constructor
  · intro h z hzsupp hodd
    by_contra hzK
    have := h z hzK hzsupp
    rw [jec_mem_leftRegion] at this
    exact this hodd
  · intro h z hzK hzsupp
    rw [jec_mem_leftRegion]
    intro hodd
    exact hzK (h z hzsupp hodd)



















theorem kc6_interiorSubset_of_supportOdd_and_noHoles (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hsupp : exc_SupportOddInK K a)
    (hbridge : kc6_OffSupportOutsideInK K a)
    (hnoHoles : kc5_OutsideOffSupportInfinite (mpl_orbitLoop K a)) :
    eaw_InteriorSubset K a :=
  kc6_interiorSubset_of_halves K a
    (kc6_offSupportReaches_of_noHoles K a R hRbox hbridge hnoHoles) hsupp



















theorem kc6_leftRegion_eq_of_core_and_winding (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hcore : eaw_InteriorSubset K a)
    (hwind : K ⊆ jec_leftRegion (mpl_orbitLoop K a)) :
    K = jec_leftRegion (mpl_orbitLoop K a) := by
  apply Set.Subset.antisymm hwind
  intro z hz
  rw [jec_mem_leftRegion] at hz
  exact hcore z hz






theorem kc6_bdEdgeMatch_of_core_and_winding (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hcore : eaw_InteriorSubset K a)
    (hwind : K ⊆ jec_leftRegion (mpl_orbitLoop K a)) :
    pww_BdEdgeMatch K (mpl_orbitLoop K a) :=
  pbs_bdEdgeMatch_of_leftRegion_eq _ (kc6_leftRegion_eq_of_core_and_winding K a hcore hwind)










theorem kc6_supportOddInK_iff_leftRegion_subset (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    exc_SupportOddInK K a ↔ kc3_LeftRegionSupportSubset K a :=
  kc3_supportOddInK_iff_leftRegion_subset





theorem kc6_interiorSubset_of_setContainments (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hsupp : kc3_LeftRegionSupportSubset K a)
    (hbridge : kc6_OffSupportOutsideInK K a)
    (hnoHoles : kc5_OutsideOffSupportInfinite (mpl_orbitLoop K a)) :
    eaw_InteriorSubset K a :=
  kc6_interiorSubset_of_supportOdd_and_noHoles K a R hRbox
    (kc6_supportOddInK_iff_leftRegion_subset K a |>.mpr hsupp) hbridge hnoHoles















theorem kc6_supportOdd_of_core_and_winding (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hcore : eaw_InteriorSubset K a)
    (hwind : K ⊆ jec_leftRegion (mpl_orbitLoop K a)) :
    exc_SupportOddInK K a :=
  kc3_core_of_bdEdgeMatch K hK a (kc6_bdEdgeMatch_of_core_and_winding K a hcore hwind)












theorem kc6_unitCell_interiorSubset : eaw_InteriorSubset unitCell ucBase :=
  eaw_unitCell_interiorSubset





theorem kc6_unitCell_leftRegion_eq :
    unitCell = jec_leftRegion (mpl_orbitLoop unitCell ucBase) :=
  kc3_unitCell_leftRegion_eq







theorem kc6_unitCell_offSupportOutsideInK : kc6_OffSupportOutsideInK unitCell ucBase := by
  intro z hzK _hzsupp
  rw [jec_mem_leftRegion, not_not]
  by_contra hodd
  exact hzK (eaw_unitCell_interiorSubset z hodd)

end Walls

end StatMech
