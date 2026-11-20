/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Code.Walls.kc10core
import Code.Walls.kc6uniqueinfinitecomponent
import Code.Lattice.ExteriorConnected
import Code.Lattice.InsideConnected

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}







theorem kc12_farLeftBeacon_mem_exterior (R : ℕ) :
    (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R :=
  exc_farLeft_mem_exterior R



theorem kc12_far_mem_exterior (R : ℕ) {w : Site 2} (hw : w 0 ≤ -((R : ℤ) + 1)) :
    w ∈ exterior 2 R :=
  ⟨0, by omega⟩











def kc12_ReachesFarLeftBeacon (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z : Site 2, z ∉ Vc.support → z ∉ jec_leftRegion Vc →
    ∃ p : (hypercubicLattice 2).Walk z ![-((R : ℤ) + 1), 0], ∀ u ∈ p.support, u ∉ Vc.support





theorem kc12_offSupportReaches_of_reachesFarLeft (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hres : kc12_ReachesFarLeftBeacon Vc R) :
    kc5_OffSupportReachesExterior Vc R := by
  intro z hzoff hzout
  obtain ⟨p, hp⟩ := hres z hzoff hzout
  refine ⟨![-((R : ℤ) + 1), 0], kc12_farLeftBeacon_mem_exterior R, ?_⟩
  have hzc : z ∈ (oc_supportSet Vc)ᶜ := by simpa [oc_supportSet] using hzoff
  rw [ffc_reachable_iff_offSupportWalk hzc]
  exact ⟨p, fun u hu => by simpa [oc_supportSet] using hp u hu⟩













theorem kc12_exterior_reaches_farLeftBeacon (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {e : Site 2} (heExt : e ∈ exterior 2 R) :
    ∃ p : (hypercubicLattice 2).Walk e ![-((R : ℤ) + 1), 0], ∀ u ∈ p.support, u ∉ Vc.support := by
  set F : Set (Site 2) := {z | z ∈ Vc.support} with hF
  have hFbox : F ⊆ box 2 R := fun q hq => hsupp ((oc_mem_supportSet Vc q).mpr hq)
  have hsub : exterior 2 R ⊆ Fᶜ := exterior_subset_compl F R hFbox
  have hbext : (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := kc12_farLeftBeacon_mem_exterior R
  have hreach := box_exterior_connected R (by norm_num) e ![-((R : ℤ) + 1), 0] heExt hbext
  have hreachF :
      ((hypercubicLattice 2).induce Fᶜ).Reachable ⟨e, hsub heExt⟩
        ⟨![-((R : ℤ) + 1), 0], hsub hbext⟩ := by
    have := hreach.map ((hypercubicLattice 2).induceHomOfLE hsub).toHom
    simpa using this
  exact exc_reachable_compl_to_offSupport_walk F (hsub heExt) (hsub hbext) hreachF







theorem kc12_reachesFarLeftBeacon_of_offSupportReaches (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (htgt : kc5_OffSupportReachesExterior Vc R) :
    kc12_ReachesFarLeftBeacon Vc R := by
  intro z hzoff hzout
  obtain ⟨e, heExt, hreach⟩ := htgt z hzoff hzout
  
  have hzc : z ∈ (oc_supportSet Vc)ᶜ := by simpa [oc_supportSet] using hzoff
  obtain ⟨p1, hp1⟩ := (ffc_reachable_iff_offSupportWalk hzc).mp hreach
  have hp1' : ∀ u ∈ p1.support, u ∉ Vc.support := fun u hu => by
    simpa [oc_supportSet] using hp1 u hu
  
  obtain ⟨p2, hp2⟩ := kc12_exterior_reaches_farLeftBeacon Vc R hsupp heExt
  refine ⟨p1.append p2, ?_⟩
  intro u hu
  rw [Walk.mem_support_append_iff] at hu
  rcases hu with h | h
  · exact hp1' u h
  · exact hp2 u h







theorem kc12_reachesFarLeftBeacon_iff_offSupportReaches (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    kc12_ReachesFarLeftBeacon Vc R ↔ kc5_OffSupportReachesExterior Vc R :=
  ⟨kc12_offSupportReaches_of_reachesFarLeft Vc R,
   kc12_reachesFarLeftBeacon_of_offSupportReaches Vc R hsupp⟩













theorem kc12_outsideOffSupportInfinite_of_reachesFarLeft (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hres : kc12_ReachesFarLeftBeacon Vc R) :
    kc5_OutsideOffSupportInfinite Vc :=
  kc8_outsideOffSupportInfinite_of_offSupportReaches Vc R hsupp
    (kc12_offSupportReaches_of_reachesFarLeft Vc R hres)







theorem kc12_reachesFarLeftBeacon_iff_outsideOffSupportInfinite
    (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    kc12_ReachesFarLeftBeacon Vc R ↔ kc5_OutsideOffSupportInfinite Vc := by
  constructor
  · exact kc12_outsideOffSupportInfinite_of_reachesFarLeft Vc R hsupp
  · intro hinf
    exact kc12_reachesFarLeftBeacon_of_offSupportReaches Vc R hsupp
      (kc5_offSupportReaches_of_corrected Vc R hsupp hinf)














theorem kc12_offSupport_reachable_offSupport (Vc : (hypercubicLattice 2).Walk a a)
    {z w : Site 2} (hz : z ∉ Vc.support) (h : (offSupport Vc).Reachable z w) :
    w ∉ Vc.support := by
  obtain ⟨p, hp⟩ := offSupport_reachable_to_offSupportWalk Vc h hz
  exact hp w p.end_mem_support


def kc12_component (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) : Set (Site 2) :=
  {y | (offSupport Vc).Reachable z y}











theorem kc12_finiteComponent_top_blocked (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hfin : (kc12_component Vc z).Finite) :
    ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 + 1] : Site 2) ∈ Vc.support := by
  classical
  obtain ⟨w, hwC, hwmax⟩ :=
    Set.exists_max_image (kc12_component Vc z) (fun y => y 1) hfin ⟨z, Reachable.refl z⟩
  have hwreach : (offSupport Vc).Reachable z w := hwC
  refine ⟨w, hwreach, ?_⟩
  by_contra hup
  have hadj : (hypercubicLattice 2).Adj w ![w 0, w 1 + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hwoff : w ∉ Vc.support := kc12_offSupport_reachable_offSupport Vc hz hwreach
  have hoffadj : (offSupport Vc).Adj w ![w 0, w 1 + 1] :=
    (offSupport_adj Vc w _).mpr ⟨hadj, hwoff, hup⟩
  have hupC : (![w 0, w 1 + 1] : Site 2) ∈ kc12_component Vc z := hwreach.trans hoffadj.reachable
  have hle := hwmax _ hupC
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hle
  omega





theorem kc12_finiteComponent_bottom_blocked (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hfin : (kc12_component Vc z).Finite) :
    ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 - 1] : Site 2) ∈ Vc.support := by
  classical
  obtain ⟨w, hwC, hwmin⟩ :=
    Set.exists_min_image (kc12_component Vc z) (fun y => y 1) hfin ⟨z, Reachable.refl z⟩
  have hwreach : (offSupport Vc).Reachable z w := hwC
  refine ⟨w, hwreach, ?_⟩
  by_contra hdown
  have hadj : (hypercubicLattice 2).Adj w ![w 0, w 1 - 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hwoff : w ∉ Vc.support := kc12_offSupport_reachable_offSupport Vc hz hwreach
  have hoffadj : (offSupport Vc).Adj w ![w 0, w 1 - 1] :=
    (offSupport_adj Vc w _).mpr ⟨hadj, hwoff, hdown⟩
  have hdownC : (![w 0, w 1 - 1] : Site 2) ∈ kc12_component Vc z := hwreach.trans hoffadj.reachable
  have hle := hwmin _ hdownC
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hle
  omega




theorem kc12_finiteComponent_right_blocked (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hfin : (kc12_component Vc z).Finite) :
    ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 + 1, w 1] : Site 2) ∈ Vc.support := by
  classical
  obtain ⟨w, hwC, hwmax⟩ :=
    Set.exists_max_image (kc12_component Vc z) (fun y => y 0) hfin ⟨z, Reachable.refl z⟩
  have hwreach : (offSupport Vc).Reachable z w := hwC
  refine ⟨w, hwreach, ?_⟩
  by_contra hright
  have hadj : (hypercubicLattice 2).Adj w ![w 0 + 1, w 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hwoff : w ∉ Vc.support := kc12_offSupport_reachable_offSupport Vc hz hwreach
  have hoffadj : (offSupport Vc).Adj w ![w 0 + 1, w 1] :=
    (offSupport_adj Vc w _).mpr ⟨hadj, hwoff, hright⟩
  have hrightC : (![w 0 + 1, w 1] : Site 2) ∈ kc12_component Vc z := hwreach.trans hoffadj.reachable
  have hle := hwmax _ hrightC
  simp only [Matrix.cons_val_zero] at hle
  omega




theorem kc12_finiteComponent_left_blocked (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hfin : (kc12_component Vc z).Finite) :
    ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 - 1, w 1] : Site 2) ∈ Vc.support := by
  classical
  obtain ⟨w, hwC, hwmin⟩ :=
    Set.exists_min_image (kc12_component Vc z) (fun y => y 0) hfin ⟨z, Reachable.refl z⟩
  have hwreach : (offSupport Vc).Reachable z w := hwC
  refine ⟨w, hwreach, ?_⟩
  by_contra hleft
  have hadj : (hypercubicLattice 2).Adj w ![w 0 - 1, w 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hwoff : w ∉ Vc.support := kc12_offSupport_reachable_offSupport Vc hz hwreach
  have hoffadj : (offSupport Vc).Adj w ![w 0 - 1, w 1] :=
    (offSupport_adj Vc w _).mpr ⟨hadj, hwoff, hleft⟩
  have hleftC : (![w 0 - 1, w 1] : Site 2) ∈ kc12_component Vc z := hwreach.trans hoffadj.reachable
  have hle := hwmin _ hleftC
  simp only [Matrix.cons_val_zero] at hle
  omega






theorem kc12_finiteComponent_enclosed (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∉ Vc.support) (hfin : (kc12_component Vc z).Finite) :
    (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 + 1] : Site 2) ∈ Vc.support) ∧
    (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 - 1] : Site 2) ∈ Vc.support) ∧
    (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 + 1, w 1] : Site 2) ∈ Vc.support) ∧
    (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 - 1, w 1] : Site 2) ∈ Vc.support) :=
  ⟨kc12_finiteComponent_top_blocked Vc hz hfin,
   kc12_finiteComponent_bottom_blocked Vc hz hfin,
   kc12_finiteComponent_right_blocked Vc hz hfin,
   kc12_finiteComponent_left_blocked Vc hz hfin⟩








theorem kc12_offSupportOutsideInfinite_of_reachesFarLeft (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hbridge : kc6_OffSupportOutsideInK K a)
    (hres : kc12_ReachesFarLeftBeacon (mpl_orbitLoop K a) R) :
    kc7_OffSupportOutsideInfinite K a :=
  kc8_offSupportOutsideInfinite_of_offSupportReaches K a R hRbox hbridge
    (kc12_offSupportReaches_of_reachesFarLeft (mpl_orbitLoop K a) R hres)





theorem kc12_unitCell_reachesFarLeftBeacon :
    kc12_ReachesFarLeftBeacon (mpl_orbitLoop unitCell ucBase) 1 :=
  kc12_reachesFarLeftBeacon_of_offSupportReaches (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc8_unitCell_offSupportReaches





theorem kc12_unitCell_offSupportReaches_via_farLeft :
    kc5_OffSupportReachesExterior (mpl_orbitLoop unitCell ucBase) 1 :=
  kc12_offSupportReaches_of_reachesFarLeft (mpl_orbitLoop unitCell ucBase) 1
    kc12_unitCell_reachesFarLeftBeacon













































end Walls

end StatMech
