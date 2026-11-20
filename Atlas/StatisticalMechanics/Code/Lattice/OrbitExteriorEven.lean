/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge

open Set SimpleGraph

namespace StatMech

namespace Lattice











theorem oee_rayParity_const_along_walk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
    (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)) := by
  induction p with
  | nil => exact Iff.rfl
  | @cons u v w hadj q ih =>
    
    have hu : u ∉ Vc.support := hp u (by simp)
    have hv : v ∉ Vc.support := hp v (by simp [SimpleGraph.Walk.support_cons])
    have htail : ∀ z ∈ q.support, z ∉ Vc.support := by
      intro z hz
      exact hp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    
    exact (jec_localConstancy Vc hadj hu hv).trans (ih htail)















theorem oee_rayCount_eq_zero_of_farLeft (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (z : Site 2)
    (hfar : ∀ p ∈ (olb_orbitLoop K hK e he).support, z 0 ≤ p 0) :
    jec_rayCount z (olb_orbitLoop K hK e he) = 0 :=
  jec_rayCount_eq_zero_of_right z (olb_orbitLoop K hK e he) hfar





theorem oee_farLeft_even (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (z : Site 2)
    (hfar : ∀ p ∈ (olb_orbitLoop K hK e he).support, z 0 ≤ p 0) :
    Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
  rw [oee_rayCount_eq_zero_of_farLeft K hK e he z hfar]
  exact Nat.even_iff.mpr rfl



















theorem oee_exterior_even (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {z z0 : Site 2}
    (p : (hypercubicLattice 2).Walk z z0)
    (hp : ∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)
    (hfar : ∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0) :
    Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
  have hbase : Even (jec_rayCount z0 (olb_orbitLoop K hK e he)) :=
    oee_farLeft_even K hK e he z0 hfar
  have hconst := oee_rayParity_const_along_walk (olb_orbitLoop K hK e he) p hp
  exact hconst.mpr hbase




















theorem oee_outsideHalf_of_exteriorEq (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0)) :
    ∀ z, z ∉ K → Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
  intro z hz
  obtain ⟨z0, p, hp, hfar⟩ := hExt z hz
  exact oee_exterior_even K hK e he p hp hfar

end Lattice

end StatMech
