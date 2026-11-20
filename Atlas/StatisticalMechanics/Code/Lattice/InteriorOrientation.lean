/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.EnclosedAreaWitness

open Set SimpleGraph Function

namespace StatMech

namespace Lattice












theorem ior_rayCount_eq_zero_of_farLeft (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, z 0 ≤ p 0) :
    jec_rayCount z (mpl_orbitLoop K a) = 0 :=
  jec_rayCount_eq_zero_of_right z (mpl_orbitLoop K a) hfar


theorem ior_farLeft_even (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, z 0 ≤ p 0) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  rw [ior_rayCount_eq_zero_of_farLeft K a z hfar]; exact Nat.even_iff.mpr rfl

















theorem ior_exterior_even (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {z z0 : Site 2} (p : (hypercubicLattice 2).Walk z z0)
    (hp : ∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)
    (hfar : ∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  have hbase : Even (jec_rayCount z0 (mpl_orbitLoop K a)) := ior_farLeft_even K a z0 hfar
  exact (oee_rayParity_const_along_walk (mpl_orbitLoop K a) p hp).mpr hbase


















def ior_ExteriorConnected (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
    (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
    (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)












theorem ior_InteriorSubset_of_exteriorConnected (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hext : ior_ExteriorConnected K a) :
    eaw_InteriorSubset K a := by
  intro z hodd
  by_contra hzK
  obtain ⟨z0, p, hp, hfar⟩ := hext z hzK
  exact hodd (ior_exterior_even K a p hp hfar)
















theorem ior_unitCell_interiorSubset : eaw_InteriorSubset unitCell ucBase :=
  eaw_unitCell_interiorSubset















theorem ior_interiorSubset_iff_leftRegion_subset (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    eaw_InteriorSubset K a ↔ jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
  constructor
  · intro h z hz
    exact h z ((jec_mem_leftRegion (mpl_orbitLoop K a) z).mp hz)
  · intro h z hodd
    exact h ((jec_mem_leftRegion (mpl_orbitLoop K a) z).mpr hodd)


















theorem ior_leftRegion_bdEdge_support (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v)) :
    u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support :=
  jec_leftRegion_bdEdge_support (mpl_orbitLoop K a) hadj hbd


















theorem ior_orbit_tail_mem (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (i : ℕ) :
    ((dartNext K)^[i] a.1).tail ∈ K :=
  (iterate_isBoundaryDart K a.1 a.2 i).tail_mem










theorem ior_windingWitness_of_tail_odd (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (htail : ∃ i : ℕ, ¬ Even (jec_rayCount ((dartNext K)^[i] a.1).tail (mpl_orbitLoop K a))) :
    wei_WindingWitness K a := by
  obtain ⟨i, hodd⟩ := htail
  exact ⟨((dartNext K)^[i] a.1).tail, ior_orbit_tail_mem K a i, hodd⟩











theorem ior_windingWitness_of_cycle_tail_odd (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (htail : ∃ i : ℕ, ¬ Even (jec_rayCount ((dartNext K)^[i] a.1).tail (mpl_orbitLoop K a))) :
    wei_WindingWitness K a :=
  ior_windingWitness_of_tail_odd K a htail

end Lattice

end StatMech
