/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.JordanContour
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.FloodFillConnected
import Code.Lattice.OutsideConnected
import Code.Lattice.ExteriorConnected

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}
















theorem kc4_exterior_reachable_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {x y : Site 2}
    (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y :=
  oc_exterior_reachable_offSupport Vc R hsupp hx hy




theorem kc4_exterior_offSupport_walk (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {x y : Site 2}
    (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support :=
  oc_farExterior_offSupport_walk Vc R hsupp hx hy













theorem kc4_exterior_mem_compl (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    z ∈ (oc_supportSet Vc)ᶜ := by
  intro hzS
  exact oc_exterior_offSupport Vc R hsupp hz (by simpa [oc_supportSet] using hzS)









theorem kc4_exterior_reachable_induce (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {x y : Site 2}
    (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).Reachable
      ⟨x, kc4_exterior_mem_compl Vc R hsupp hx⟩ ⟨y, kc4_exterior_mem_compl Vc R hsupp hy⟩ := by
  obtain ⟨p, hp⟩ := kc4_exterior_offSupport_walk Vc R hsupp hx hy
  refine walk_induce_reachable (hypercubicLattice 2) (oc_supportSet Vc)ᶜ p (fun z hz => ?_)
    (kc4_exterior_mem_compl Vc R hsupp hx) (kc4_exterior_mem_compl Vc R hsupp hy)
  
  intro hzS
  exact hp z hz (by simpa [oc_supportSet] using hzS)

















theorem kc4_orbit_exterior_reachable_induce (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    ((hypercubicLattice 2).induce
        ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable
      ⟨x, exterior_subset_compl _ R hRbox hx⟩ ⟨y, exterior_subset_compl _ R hRbox hy⟩ := by
  
  have hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R := hRbox
  have h := kc4_exterior_reachable_induce (mpl_orbitLoop K a) R hsupp hx hy
  
  exact h





theorem kc4_orbit_exterior_offSupport_walk (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    ∃ p : (hypercubicLattice 2).Walk x y,
      ∀ z ∈ p.support, z ∉ (mpl_orbitLoop K a).support :=
  kc4_exterior_offSupport_walk (mpl_orbitLoop K a) R hRbox hx hy









theorem kc4_orbit_loopSupportBox (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    ∃ R : ℕ, ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R :=
  exc_exists_loopSupportBox K a




theorem kc4_orbit_exterior_reachable_induce_exists (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    ∃ R : ℕ, ∃ hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R,
      ∀ x y : Site 2, ∀ (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R),
        ((hypercubicLattice 2).induce
            ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable
          ⟨x, exterior_subset_compl _ R hRbox hx⟩ ⟨y, exterior_subset_compl _ R hRbox hy⟩ := by
  obtain ⟨R, hRbox⟩ := kc4_orbit_loopSupportBox K a
  exact ⟨R, hRbox, fun x y hx hy => kc4_orbit_exterior_reachable_induce K a R hRbox hx hy⟩

end Walls

end StatMech
