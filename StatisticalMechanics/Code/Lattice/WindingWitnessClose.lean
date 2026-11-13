/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanEnclosure
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.UmlaufsatzSingleCycle
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.WindingEarInduction
import Code.Lattice.EnclosedAreaWitness

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

























theorem wwc_outside_even_of_exterior (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  intro z hz
  obtain ⟨z0, p, hp, hfar⟩ := hExt z hz
  
  have hbase : Even (jec_rayCount z0 (mpl_orbitLoop K a)) := by
    rw [jec_rayCount_eq_zero_of_right z0 (mpl_orbitLoop K a) hfar]
    exact Nat.even_iff.mpr rfl
  
  exact (oee_rayParity_const_along_walk (mpl_orbitLoop K a) p hp).mpr hbase









theorem wwc_leftRegion_subset_of_exterior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
  intro z hz
  rw [jec_mem_leftRegion] at hz
  by_contra hzK
  exact hz (wwc_outside_even_of_exterior K a hExt z hzK)














theorem wwc_interiorSubset_of_exterior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    eaw_InteriorSubset K a :=
  fun z hz => wwc_leftRegion_subset_of_exterior K a hExt (jec_mem_leftRegion _ z |>.mpr hz)




























theorem wwc_windingWitness_of_cycle_exterior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a)))
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    wei_WindingWitness K a := by
  
  have hcyc : (mpl_orbitLoop K a).IsCycle := mpl_orbitLoop_isCycle K a hp hinj
  
  obtain ⟨z0, hz0⟩ := eaw_cycle_oddCell' (mpl_orbitLoop K a) hcyc
  
  exact ⟨z0, wwc_leftRegion_subset_of_exterior K a hExt ((jec_mem_leftRegion _ z0).mpr hz0), hz0⟩





theorem wwc_windingWitness_of_noPinch_exterior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    wei_WindingWitness K a :=
  wwc_windingWitness_of_cycle_exterior K a hp (orbitFace_injOn_of_noPinch K a hnp) hExt














theorem wwc_loopWindsRegion_conjuncts_of_exterior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a ∧ eaw_InteriorSubset K a :=
  ⟨hp, hnp, wwc_interiorSubset_of_exterior K a hExt⟩








theorem wwc_loopWindsRegion_of_exterior
    (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a →
        3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
    (hExt : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a →
        ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
          (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    eaw_LoopWindsRegion := by
  intro K hK hge a hsat
  obtain ⟨hp, hnp⟩ := hcyc K hK hge a hsat
  exact wwc_loopWindsRegion_conjuncts_of_exterior K a hp hnp (hExt K hK hge a hsat)














theorem wwc_windingSaturatingWitness_of_exterior
    (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a →
        3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
    (hExt : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a →
        ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
          (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    wei_WindingSaturatingWitness :=
  eaw_windingSaturatingWitness_of_residue (wwc_loopWindsRegion_of_exterior hcyc hExt)






theorem wwc_starHull_windingWitness_of_exterior
    (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a →
        3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
    (hExt : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a →
        ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
          (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0))
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    wei_WindingWitness (ndt_StarHull K) a :=
  eaw_starHull_windingWitness_of_residue
    (wwc_loopWindsRegion_of_exterior hcyc hExt) K hSK hne a





















theorem wwc_unitCell_windingWitness : wei_WindingWitness unitCell ucBase := by
  
  obtain ⟨hp4, hnp, hint⟩ := eaw_unitCell_loopWindsRegion
  have hcyc : (mpl_orbitLoop unitCell ucBase).IsCycle :=
    mpl_orbitLoop_isCycle unitCell ucBase hp4 (orbitFace_injOn_of_noPinch unitCell ucBase hnp)
  obtain ⟨z0, hz0⟩ := eaw_cycle_oddCell' (mpl_orbitLoop unitCell ucBase) hcyc
  
  exact ⟨z0, hint z0 hz0, hz0⟩

end Lattice

end StatMech
