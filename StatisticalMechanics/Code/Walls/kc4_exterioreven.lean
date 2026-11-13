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
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.ExteriorConnected
import Code.Lattice.MinimalPeriodLoop
import Code.Walls.kc3_exterioreven

open Set SimpleGraph Function
open StatMech.Lattice

namespace StatMech.Walls












theorem kc4_farLeft_rayCount_zero {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
    jec_rayCount z Vc = 0 :=
  jec_rayCount_eq_zero_of_right z Vc hfar




theorem kc4_farLeft_even {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
    Even (jec_rayCount z Vc) := by
  rw [kc4_farLeft_rayCount_zero Vc z hfar]; exact ⟨0, rfl⟩




theorem kc4_farLeft_not_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not]
  exact kc4_farLeft_even Vc z hfar


















theorem kc4_exterior_reaches_farLeft {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hR : ({z | z ∈ Vc.support} : Set (Site 2)) ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ Vc.support) ∧ (∀ q ∈ Vc.support, z0 0 ≤ q 0) := by
  obtain ⟨z0, p, hp, hfar⟩ :=
    exc_exterior_reaches_farLeft ({z | z ∈ Vc.support} : Set (Site 2)) R hR z hz
  exact ⟨z0, p, fun w hw hwsupp => hp w hw hwsupp, fun q hq => hfar q hq⟩
















theorem kc4_exterior_even {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hR : ({z | z ∈ Vc.support} : Set (Site 2)) ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    Even (jec_rayCount z Vc) := by
  obtain ⟨z0, p, hp, hfar⟩ := kc4_exterior_reaches_farLeft Vc R hR z hz
  exact (kc3_rayParity_const_along_walk Vc p hp).mpr (kc4_farLeft_even Vc z0 hfar)





theorem kc4_exterior_not_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hR : ({z | z ∈ Vc.support} : Set (Site 2)) ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not]
  exact kc4_exterior_even Vc R hR z hz














theorem kc4_orbitLoop_exterior_even (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (R : ℕ) (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) :=
  kc4_exterior_even (mpl_orbitLoop K a) R hR z hz





theorem kc4_orbitLoop_exterior_not_mem_leftRegion (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    z ∉ jec_leftRegion (mpl_orbitLoop K a) :=
  kc4_exterior_not_mem_leftRegion (mpl_orbitLoop K a) R hR z hz





















theorem kc4_exteriorEven_node :
    (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2),
        (∀ p ∈ Vc.support, z 0 ≤ p 0) → jec_rayCount z Vc = 0)
    ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ),
        ({z | z ∈ Vc.support} : Set (Site 2)) ⊆ box 2 R →
        ∀ z ∈ exterior 2 R, ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support, w ∉ Vc.support) ∧ (∀ q ∈ Vc.support, z0 0 ≤ q 0))
    ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ),
        ({z | z ∈ Vc.support} : Set (Site 2)) ⊆ box 2 R →
        ∀ z ∈ exterior 2 R, z ∉ jec_leftRegion Vc) :=
  ⟨fun _ Vc z hfar => kc4_farLeft_rayCount_zero Vc z hfar,
   fun _ Vc R hR z hz => kc4_exterior_reaches_farLeft Vc R hR z hz,
   fun _ Vc R hR z hz => kc4_exterior_not_mem_leftRegion Vc R hR z hz⟩

end StatMech.Walls
