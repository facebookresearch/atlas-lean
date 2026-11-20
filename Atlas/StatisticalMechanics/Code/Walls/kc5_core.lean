/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Code.Walls.kc4_core

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}







def kc5_OutsideOffSupportInfinite (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ (z : Site 2), z ∉ Vc.support → z ∉ jec_leftRegion Vc →
    ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
      (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite




theorem kc5_offSupportInfinite_of_outsideInfinite (Vc : (hypercubicLattice 2).Walk a a)
    (h : kc4_OutsideInInfiniteComponent Vc) : kc5_OutsideOffSupportInfinite Vc :=
  fun z _ hzout => h z hzout









theorem kc5_outsideInfinite_forces_supportOdd (Vc : (hypercubicLattice 2).Walk a a)
    (h : kc4_OutsideInInfiniteComponent Vc) :
    ∀ z ∈ Vc.support, ¬ Even (jec_rayCount z Vc) := by
  intro z hz hev
  have hzout : z ∉ jec_leftRegion Vc := by
    rw [jec_mem_leftRegion]; exact not_not.mpr hev
  obtain ⟨hzmem, _⟩ := h z hzout
  simp only [Set.mem_compl_iff, oc_mem_supportSet] at hzmem
  exact hzmem hz






theorem kc5_outsideInfinite_iff_offSupport_and_supportOdd (Vc : (hypercubicLattice 2).Walk a a) :
    kc4_OutsideInInfiniteComponent Vc ↔
      (kc5_OutsideOffSupportInfinite Vc ∧ ∀ z ∈ Vc.support, ¬ Even (jec_rayCount z Vc)) := by
  constructor
  · intro h
    exact ⟨kc5_offSupportInfinite_of_outsideInfinite Vc h,
           kc5_outsideInfinite_forces_supportOdd Vc h⟩
  · rintro ⟨hoff, hpar⟩ z hzout
    have heven : Even (jec_rayCount z Vc) := by
      rw [jec_mem_leftRegion] at hzout; exact not_not.mp hzout
    have hzoff : z ∉ Vc.support := fun hzs => hpar z hzs heven
    exact hoff z hzoff hzout







def kc5_OffSupportReachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z, z ∉ Vc.support → z ∉ jec_leftRegion Vc →
    ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e





theorem kc5_offSupportReaches_of_corrected (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : kc5_OutsideOffSupportInfinite Vc) :
    kc5_OffSupportReachesExterior Vc R := by
  intro z hoff hout
  obtain ⟨hzmem, hinf⟩ := h z hoff hout
  exact kc4_reaches_exterior_of_infiniteComponent Vc R hsupp hzmem hinf






theorem kc5_corrected_seed (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    z ∉ Vc.support ∧ z ∉ jec_leftRegion Vc ∧
      ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
        (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
          ⟨z, hzmem⟩).supp.Infinite := by
  obtain ⟨hout, hzmem, hinf⟩ := kc4_residue_nonvacuous Vc R hsupp hz
  have hoff : z ∉ Vc.support := by
    simpa only [Set.mem_compl_iff, oc_mem_supportSet] using hzmem
  exact ⟨hoff, hout, hzmem, hinf⟩




theorem kc5_corrected_conclusion_seed (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
      (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite :=
  (kc5_corrected_seed Vc R hsupp hz).2.2

end Walls

end StatMech
