/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.EnclosedAreaWitness
import Code.Lattice.ExteriorConnected
import Code.Lattice.WindingWitnessClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice
















theorem ecd_wwcExt_false :
    ¬ (∀ z, z ∉ unitCell → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop unitCell ucBase).support) ∧
        (∀ q ∈ (mpl_orbitLoop unitCell ucBase).support, z0 0 ≤ q 0)) := by
  intro h
  obtain ⟨z0, p, hp, _⟩ := h _ exc_unitCell_offK_notMem
  exact hp _ p.start_mem_support exc_unitCell_offK_on_support














theorem ecd_exterior_reaches_farLeft (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (R : ℕ) (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) :=
  exc_exterior_reaches_farLeft ({z | z ∈ (mpl_orbitLoop K a).support}) R hR z hz
















theorem ecd_interiorSubset_of_exc (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a) (hsupp : exc_SupportOddInK K a) :
    eaw_InteriorSubset K a :=
  exc_interiorSubset_of_reaches_and_support K a hoff hsupp






theorem ecd_leftRegion_subset_of_exc (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a) (hsupp : exc_SupportOddInK K a) :
    jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
  intro z hz
  rw [jec_mem_leftRegion] at hz
  exact ecd_interiorSubset_of_exc K a hoff hsupp z hz





















theorem ecd_windingWitness_of_cycle_exc (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hoff : exc_OffSupportReachesExterior K a) (hsupp : exc_SupportOddInK K a) :
    wei_WindingWitness K a :=
  eaw_windingWitness_of_cycle_interior K a hp hnp (ecd_interiorSubset_of_exc K a hoff hsupp)












theorem ecd_loopWindsRegion_conjuncts_of_exc (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hoff : exc_OffSupportReachesExterior K a) (hsupp : exc_SupportOddInK K a) :
    3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a ∧ eaw_InteriorSubset K a :=
  ⟨hp, hnp, ecd_interiorSubset_of_exc K a hoff hsupp⟩







theorem ecd_loopWindsRegion_of_exc
    (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a →
        3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
    (hoff : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a → exc_OffSupportReachesExterior K a)
    (hsupp : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a → exc_SupportOddInK K a) :
    eaw_LoopWindsRegion := by
  intro K hK hge a hsat
  obtain ⟨hp, hnp⟩ := hcyc K hK hge a hsat
  exact ecd_loopWindsRegion_conjuncts_of_exc K a hp hnp
    (hoff K hK hge a hsat) (hsupp K hK hge a hsat)






theorem ecd_windingSaturatingWitness_of_exc
    (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a →
        3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
    (hoff : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a → exc_OffSupportReachesExterior K a)
    (hsupp : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a → exc_SupportOddInK K a) :
    wei_WindingSaturatingWitness :=
  eaw_windingSaturatingWitness_of_residue (ecd_loopWindsRegion_of_exc hcyc hoff hsupp)





theorem ecd_starHull_windingWitness_of_exc
    (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a →
        3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
    (hoff : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a → exc_OffSupportReachesExterior K a)
    (hsupp : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
      ∀ (a : {e : Dart // IsBoundaryDart K e}),
        K ⊆ bpc_orbitFootprint K a → exc_SupportOddInK K a)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    wei_WindingWitness (ndt_StarHull K) a :=
  eaw_starHull_windingWitness_of_residue (ecd_loopWindsRegion_of_exc hcyc hoff hsupp) K hSK hne a
















theorem ecd_unitCell_windingWitness : wei_WindingWitness unitCell ucBase := by
  obtain ⟨hp, hnp, hint⟩ := eaw_unitCell_loopWindsRegion
  exact eaw_windingWitness_of_cycle_interior unitCell ucBase hp hnp hint

end Lattice

end StatMech
