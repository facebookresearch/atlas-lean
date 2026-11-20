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
import Code.Lattice.EulerGeometricFaces
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.FloodFillConnected
import Code.Lattice.OutsideConnected

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}











theorem ocov_beacon_mem_exterior (R : ℕ) : beacon 2 R ∈ exterior 2 R :=
  beacon_mem_exterior R (by norm_num)



theorem ocov_beacon_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    beacon 2 R ∉ Vc.support :=
  oc_exterior_offSupport Vc R hsupp (ocov_beacon_mem_exterior R)


theorem ocov_beacon_in_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) :
    beacon 2 R ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) :=
  ffc_seed_mem_floodFill (oc_supportSet Vc) (beacon 2 R)





theorem ocov_exterior_in_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  rw [ffc_mem_floodFill]
  
  exact (oc_exterior_reachable_offSupport Vc R hsupp (ocov_beacon_mem_exterior R) hz)



theorem ocov_exterior_subset_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    exterior 2 R ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) :=
  fun _ hz => ocov_exterior_in_beaconFill Vc R hsupp hz













theorem ocov_in_beaconFill_of_reaches_exterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z e : Site 2} (he : e ∈ exterior 2 R)
    (hze : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
    z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  rw [ffc_mem_floodFill]
  
  have hbe : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable (beacon 2 R) e :=
    oc_exterior_reachable_offSupport Vc R hsupp (ocov_beacon_mem_exterior R) he
  exact hbe.trans hze.symm





theorem ocov_row_ge_R_in_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hzrow : (R : ℤ) ≤ z 1) (hzoff : z ∉ Vc.support) :
    z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  obtain ⟨e, he, hze⟩ := oc_reachesExterior_of_row_ge_R Vc R hsupp hzrow hzoff
  exact ocov_in_beaconFill_of_reaches_exterior Vc R hsupp he hze











theorem ocov_beacon_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    beacon 2 R ∉ jec_leftRegion Vc :=
  egf_exterior_outside Vc R hsupp (ocov_beacon_mem_exterior R)






theorem ocov_beaconFill_mem_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2}
    (hz : z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :
    z ∉ jec_leftRegion Vc := by
  rw [ffc_mem_floodFill] at hz
  have hsupp' : oc_supportSet Vc ⊆ box 2 R := fun p hp => hsupp p hp
  
  obtain ⟨pw, hpw⟩ :=
    (oc_offSupportLattice_reachable_iff Vc (ocov_beacon_offSupport Vc R hsupp')).mp hz
  
  have hsame := jlri_sameRegion_along_offSupport_walk Vc pw hpw
  intro hzin
  exact ocov_beacon_outside Vc R hsupp (hsame.mpr hzin)



theorem ocov_beaconFill_subset_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    ffc_floodFill (oc_supportSet Vc) (beacon 2 R) ⊆ (jec_leftRegion Vc)ᶜ :=
  fun _ hz => ocov_beaconFill_mem_outside Vc R hsupp hz













theorem ocov_reachesExterior_of_in_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2} (hz : z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  rw [ffc_mem_floodFill] at hz
  exact ⟨beacon 2 R, ocov_beacon_mem_exterior R, hz.symm⟩









theorem ocov_reachesExterior_iff_in_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2} :
    (∃ e : Site 2, e ∈ exterior 2 R ∧
        (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e)
      ↔ z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  constructor
  · rintro ⟨e, he, hze⟩
    exact ocov_in_beaconFill_of_reaches_exterior Vc R hsupp he hze
  · intro hz
    exact ocov_reachesExterior_of_in_beaconFill Vc R hz










theorem ocov_outsideReachesExterior_iff_beaconCovers (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    oc_OutsideReachesExterior Vc R ↔
      (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  constructor
  · intro h z hz
    have hz' : z ∉ jec_leftRegion Vc := hz
    exact (ocov_reachesExterior_iff_in_beaconFill Vc R hsupp).mp (h z hz')
  · intro hcov z hz
    exact (ocov_reachesExterior_iff_in_beaconFill Vc R hsupp).mpr (hcov hz)





theorem ocov_beaconFill_eq_outside_iff (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    ffc_floodFill (oc_supportSet Vc) (beacon 2 R) = (jec_leftRegion Vc)ᶜ ↔
      (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  constructor
  · intro h; rw [h]
  · intro hcov
    exact le_antisymm (ocov_beaconFill_subset_outside Vc R hsupp) hcov












theorem ocov_hOutOff_of_beaconCovers (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hcov : (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :
    ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
      ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support :=
  oc_hOutOff_of_reachesExterior Vc R hsupp
    ((ocov_outsideReachesExterior_iff_beaconCovers Vc R hsupp).mpr hcov)












theorem ocov_two_components_of_beaconCovers (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    (hcov : (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  oc_two_components_of_outsideReaches Vc R hsupp hp hq hInOff
    ((ocov_outsideReachesExterior_iff_beaconCovers Vc R hsupp).mpr hcov)















theorem ocov_beaconFill_nonvacuous (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    beacon 2 R ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) ∧
      exterior 2 R ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) ∧
      (∀ z : Site 2, (R : ℤ) ≤ z 1 → z ∉ Vc.support →
        z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :=
  ⟨ocov_beacon_in_beaconFill Vc R,
   ocov_exterior_subset_beaconFill Vc R hsupp,
   fun _ hzrow hzoff => ocov_row_ge_R_in_beaconFill Vc R hsupp hzrow hzoff⟩







theorem ocov_beaconCovers_of_outsideExteriorOrHigh (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hall : ∀ z : Site 2, z ∉ jec_leftRegion Vc →
        z ∈ exterior 2 R ∨ ((R : ℤ) ≤ z 1 ∧ z ∉ Vc.support)) :
    (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  intro z hz
  have hz' : z ∉ jec_leftRegion Vc := hz
  rcases hall z hz' with hext | ⟨hrow, hoff⟩
  · exact ocov_exterior_in_beaconFill Vc R hsupp hext
  · exact ocov_row_ge_R_in_beaconFill Vc R hsupp hrow hoff

end Lattice

end StatMech
