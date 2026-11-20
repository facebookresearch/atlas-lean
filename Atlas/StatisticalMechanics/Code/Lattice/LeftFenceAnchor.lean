/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.WindingEarInduction
import Code.Lattice.EnclosedAreaWitness
import Code.Lattice.StarHullWinding
import Code.Lattice.StarHullFinite
import Code.Lattice.StarHullTurning
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.LexMinOrientation
import Code.Lattice.OrbitCoversBoundary

open Set SimpleGraph Function

namespace StatMech

namespace Lattice













theorem lfa_leftFence_anchor (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ z₀ ∈ K, IsBoundaryDart K (lmo_leftDartAt z₀) ∧ (∀ w ∈ K, z₀ 0 ≤ w 0) := by
  obtain ⟨z₀, hz₀, hbd, _hdir, _htail, hmin⟩ := ocb_leftFence_data K hK hne
  exact ⟨z₀, hz₀, hbd, hmin⟩














theorem lfa_leftFence_on_own_orbit (K : Set (Site 2)) (z₀ : Site 2)
    (hbd : IsBoundaryDart K (lmo_leftDartAt z₀)) :
    ∃ n : ℕ, (dartNext K)^[n] (⟨lmo_leftDartAt z₀, hbd⟩ : {e : Dart // IsBoundaryDart K e}).1
      = lmo_leftDartAt z₀ :=
  ⟨0, by simp⟩











theorem lfa_leftFence_reachesLeftmost (K : Set (Site 2)) (hK : K.Finite) (z₀ : Site 2)
    (hbd : IsBoundaryDart K (lmo_leftDartAt z₀)) (m : ℤ) (hm : z₀ 0 = m) :
    lmo_OrbitReachesLeftmost K ⟨lmo_leftDartAt z₀, hbd⟩ m :=
  ocb_reachesLeftmost_of_leftFence_on_orbit K hK ⟨lmo_leftDartAt z₀, hbd⟩ z₀ m hm
    (lfa_leftFence_on_own_orbit K z₀ hbd)




















theorem lfa_leftFence_windingWitness (K : Set (Site 2)) (hK : K.Finite) (z₀ : Site 2)
    (hbd : IsBoundaryDart K (lmo_leftDartAt z₀)) (m : ℤ) (hm : z₀ 0 = m)
    (hmin : ∀ w ∈ K, m ≤ w 0)
    (hcyc : (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).IsCycle) :
    wei_WindingWitness K ⟨lmo_leftDartAt z₀, hbd⟩ :=
  lmo_windingWitness_of_reachesLeftmost K ⟨lmo_leftDartAt z₀, hbd⟩ m hmin hcyc
    (lfa_leftFence_reachesLeftmost K hK z₀ hbd m hm)







theorem lfa_exists_anchor_windingWitness (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (hcyc : ∀ z₀ : Site 2, ∀ hbd : IsBoundaryDart K (lmo_leftDartAt z₀),
      (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).IsCycle) :
    ∃ a : {e : Dart // IsBoundaryDart K e}, wei_WindingWitness K a := by
  obtain ⟨z₀, _hz₀, hbd, hmin⟩ := lfa_leftFence_anchor K hK hne
  exact ⟨⟨lmo_leftDartAt z₀, hbd⟩,
    lfa_leftFence_windingWitness K hK z₀ hbd (z₀ 0) rfl hmin (hcyc z₀ hbd)⟩


















theorem lfa_starHull_leftFence_windingWitness (K : Set (Site 2)) (hK : K.Finite) (z₀ : Site 2)
    (hbd : IsBoundaryDart (ndt_StarHull K) (lmo_leftDartAt z₀)) (m : ℤ) (hm : z₀ 0 = m)
    (hmin : ∀ w ∈ ndt_StarHull K, m ≤ w 0)
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩) :
    wei_WindingWitness (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩ :=
  lfa_leftFence_windingWitness (ndt_StarHull K) (starHull_finite K hK) z₀ hbd m hm hmin
    (shw_starHull_mpl_isCycle K ⟨lmo_leftDartAt z₀, hbd⟩ hp)






theorem lfa_starHull_exists_anchor_windingWitness (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty)
    (hp : ∀ z₀ : Site 2, ∀ hbd : IsBoundaryDart (ndt_StarHull K) (lmo_leftDartAt z₀),
      3 ≤ dartOrbitPeriod (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩) :
    ∃ a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e},
      wei_WindingWitness (ndt_StarHull K) a := by
  obtain ⟨z₀, _hz₀, hbd, hmin⟩ :=
    lfa_leftFence_anchor (ndt_StarHull K) (starHull_finite K hK) (sht_starHull_nonempty K hne)
  exact ⟨⟨lmo_leftDartAt z₀, hbd⟩,
    lfa_starHull_leftFence_windingWitness K hK z₀ hbd (z₀ 0) rfl hmin (hp z₀ hbd)⟩























theorem lfa_windingWitness_of_interiorSubset_and_enclosed (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hint : eaw_InteriorSubset K a)
    (henc : ∃ z : Site 2, ¬ Even (jec_rayCount z (mpl_orbitLoop K a))) :
    wei_WindingWitness K a := by
  obtain ⟨z, hz⟩ := henc
  exact ⟨z, hint z hz, hz⟩







theorem lfa_consumer_needs_interiorSubset (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hint : eaw_InteriorSubset K a) :
    wei_WindingWitness K a :=
  eaw_windingWitness_of_cycle_interior K a hp hnp hint

















theorem lfa_distinct_dart_same_orbit_not_reflexive (K : Set (Site 2))
    {e f : Dart} (hne : e ≠ f) :
    ¬ ((dartNext K)^[0] e = f) := by
  simpa using hne


















theorem lfa_foreign_anchor_needs_interfaceConnected (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (z₀ : Site 2)
    (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
    (hInt : InterfaceConnected K)
    (hcomp : ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨a.1.head, a.2.2⟩ ⟨(lmo_leftDartAt z₀).head, hbd.2⟩) :
    ∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀ :=
  ocb_leftFence_on_orbit_of_sameComponent a hbd hInt hcomp









theorem lfa_unitCell_leftFence_isBoundaryDart :
    IsBoundaryDart unitCell (lmo_leftDartAt (![0, 0] : Site 2)) := by
  apply lmo_leftDartAt_isBoundaryDart
  · rw [unitCell, Set.mem_singleton_iff]
  · rw [unitCell, Set.mem_singleton_iff]
    intro h
    have := congrFun h 0
    simp at this





theorem lfa_unitCell_leftFence_reachesLeftmost :
    lmo_OrbitReachesLeftmost unitCell ⟨lmo_leftDartAt (![0, 0] : Site 2),
      lfa_unitCell_leftFence_isBoundaryDart⟩ 0 :=
  lfa_leftFence_reachesLeftmost unitCell (Set.finite_singleton _) (![0, 0] : Site 2)
    lfa_unitCell_leftFence_isBoundaryDart 0 (by simp)


























































end Lattice

end StatMech
