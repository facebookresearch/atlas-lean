/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.OrbitInteriorOdd
import Code.Lattice.ClosedContourSeparation
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.WindingWitness

open SimpleGraph Function Set

namespace StatMech

namespace Lattice













theorem jsp_odd_propagates_off_support (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (i : ℕ) {z₀ : Site 2}
    (p : (hypercubicLattice 2).Walk ((dartNext K)^[i] a.1).tail z₀)
    (hp : ∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK a.1 a.2).support)
    (hodd : ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2))) :
    ¬ Even (jec_rayCount ((dartNext K)^[i] a.1).tail (olb_orbitLoop K hK a.1 a.2)) :=
  ooi_odd_of_connected_to_odd (olb_orbitLoop K hK a.1 a.2) p hp hodd


















theorem jsp_tailOdd_of_oddCell_reaches_tail (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) {z₀ : Site 2} (i : ℕ)
    (p : (hypercubicLattice 2).Walk ((dartNext K)^[i] a.1).tail z₀)
    (hp : ∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK a.1 a.2).support)
    (hodd : ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2))) :
    wwit_TailOdd K hK a :=
  ⟨i, jsp_odd_propagates_off_support K hK a i p hp hodd⟩



















def jsp_OrbitWinds (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∃ (i : ℕ) (z₀ : Site 2) (p : (hypercubicLattice 2).Walk ((dartNext K)^[i] a.1).tail z₀),
    (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK a.1 a.2).support) ∧
    ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2))





theorem jsp_tailOdd_of_orbitWinds (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hwind : jsp_OrbitWinds K hK a) :
    wwit_TailOdd K hK a := by
  obtain ⟨i, z₀, p, hp, hodd⟩ := hwind
  exact jsp_tailOdd_of_oddCell_reaches_tail K hK a i p hp hodd





theorem jsp_winding_witness_of_orbitWinds (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hwind : jsp_OrbitWinds K hK a) :
    ∃ z₀ : Site 2, z₀ ∈ K ∧
      ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2)) :=
  wwit_winding_witness_of_tailOdd K hK a (jsp_tailOdd_of_orbitWinds K hK a hwind)












theorem jsp_starHull_tailOdd_of_orbitWinds (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hwind : jsp_OrbitWinds (ndt_StarHull K) hSK a) :
    wwit_TailOdd (ndt_StarHull K) hSK a :=
  jsp_tailOdd_of_orbitWinds (ndt_StarHull K) hSK a hwind





theorem jsp_starHull_winding_witness_of_orbitWinds (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hwind : jsp_OrbitWinds (ndt_StarHull K) hSK a) :
    ∃ z₀ : Site 2, z₀ ∈ ndt_StarHull K ∧
      ¬ Even (jec_rayCount z₀ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2)) :=
  jsp_winding_witness_of_orbitWinds (ndt_StarHull K) hSK a hwind























theorem jsp_two_component_separation (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p (olb_orbitLoop K hK a.1 a.2)))
    (hq : ∀ w ∈ (olb_orbitLoop K hK a.1 a.2).support, w 0 ≤ q 0 - 1)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion (olb_orbitLoop K hK a.1 a.2) →
        t ∈ jec_leftRegion (olb_orbitLoop K hK a.1 a.2) →
        (latticeMinusBarrier (jec_leftRegion (olb_orbitLoop K hK a.1 a.2))).Reachable s t)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion (olb_orbitLoop K hK a.1 a.2) →
        t ∉ jec_leftRegion (olb_orbitLoop K hK a.1 a.2) →
        (latticeMinusBarrier (jec_leftRegion (olb_orbitLoop K hK a.1 a.2))).Reachable s t) :
    Nat.card (latticeMinusBarrier (jec_leftRegion (olb_orbitLoop K hK a.1 a.2))).ConnectedComponent
      = 2 :=
  ccs_closedLoop_two_components (olb_orbitLoop K hK a.1 a.2) hp hq hin hout













theorem jsp_orbitWinds_oddRay_satisfiable :
    ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) :=
  wwit_unitSquareLoop_inside_odd






































end Lattice

end StatMech
