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

open Set SimpleGraph Function
open StatMech.Lattice

namespace StatMech.Walls













theorem kc3_rayCount_eq_zero_of_farLeft {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
    jec_rayCount z Vc = 0 :=
  jec_rayCount_eq_zero_of_right z Vc hfar




theorem kc3_farLeft_even {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
    Even (jec_rayCount z Vc) := by
  rw [kc3_rayCount_eq_zero_of_farLeft Vc z hfar]
  exact Nat.even_iff.mpr rfl





theorem kc3_farLeft_not_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not]
  exact kc3_farLeft_even Vc z hfar












theorem kc3_rayParity_const_along_walk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
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

















theorem kc3_exterior_even {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z z0 : Site 2} (p : (hypercubicLattice 2).Walk z z0)
    (hp : ∀ w ∈ p.support, w ∉ Vc.support)
    (hfar : ∀ q ∈ Vc.support, z0 0 ≤ q 0) :
    Even (jec_rayCount z Vc) :=
  (kc3_rayParity_const_along_walk Vc p hp).mpr (kc3_farLeft_even Vc z0 hfar)




theorem kc3_exterior_even_of_reachesFarLeft {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2}
    (h : ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ Vc.support) ∧ (∀ q ∈ Vc.support, z0 0 ≤ q 0)) :
    Even (jec_rayCount z Vc) := by
  obtain ⟨z0, p, hp, hfar⟩ := h
  exact kc3_exterior_even Vc p hp hfar




theorem kc3_exterior_not_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z z0 : Site 2} (p : (hypercubicLattice 2).Walk z z0)
    (hp : ∀ w ∈ p.support, w ∉ Vc.support)
    (hfar : ∀ q ∈ Vc.support, z0 0 ≤ q 0) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not]
  exact kc3_exterior_even Vc p hp hfar



















theorem kc3_exteriorEven_node :
    (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2),
        (∀ p ∈ Vc.support, z 0 ≤ p 0) → jec_rayCount z Vc = 0)
    ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (x y : Site 2)
        (p : (hypercubicLattice 2).Walk x y), (∀ z ∈ p.support, z ∉ Vc.support) →
        (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)))
    ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z z0 : Site 2)
        (p : (hypercubicLattice 2).Walk z z0), (∀ w ∈ p.support, w ∉ Vc.support) →
        (∀ q ∈ Vc.support, z0 0 ≤ q 0) → Even (jec_rayCount z Vc)) :=
  ⟨fun _ Vc z hfar => kc3_rayCount_eq_zero_of_farLeft Vc z hfar,
   fun _ Vc _ _ p hp => kc3_rayParity_const_along_walk Vc p hp,
   fun _ Vc _ _ p hp hfar => kc3_exterior_even Vc p hp hfar⟩

end StatMech.Walls
