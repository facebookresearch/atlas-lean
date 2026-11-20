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
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.FloodFillConnected
import Code.Lattice.OutsideConnected
import Code.Lattice.EnclosedAreaWitness
import Code.Lattice.ExteriorConnected

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice












theorem kc3_offSupportWalk_to_inducedReachable (F : Set (Site 2)) {z e : Site 2}
    (hz : z ∈ Fᶜ) (he : e ∈ Fᶜ)
    (p : (hypercubicLattice 2).Walk z e) (hp : ∀ w ∈ p.support, w ∉ F) :
    ((hypercubicLattice 2).induce Fᶜ).Reachable ⟨z, hz⟩ ⟨e, he⟩ :=
  walk_induce_reachable (hypercubicLattice 2) Fᶜ p (fun w hw => hp w hw) hz he











theorem kc3_inducedReachable_of_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z e : Site 2} (hz : z ∉ ({z | z ∈ Vc.support} : Set (Site 2)))
    (h : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
    ∃ he : e ∈ ({z | z ∈ Vc.support} : Set (Site 2))ᶜ,
      ((hypercubicLattice 2).induce ({z | z ∈ Vc.support} : Set (Site 2))ᶜ).Reachable
        ⟨z, hz⟩ ⟨e, he⟩ := by
  
  have hzB : z ∉ oc_supportSet Vc := hz
  obtain ⟨p, hp⟩ := (ffc_reachable_iff_offSupportWalk (B := oc_supportSet Vc) hzB).mp h
  
  have heB : e ∉ ({z | z ∈ Vc.support} : Set (Site 2)) := hp e p.end_mem_support
  refine ⟨heB, ?_⟩
  exact kc3_offSupportWalk_to_inducedReachable ({z | z ∈ Vc.support}) hz heB p
    (fun w hw => hp w hw)
































theorem kc3_offSupportReachesExterior_of_interiorSubset_and_outside (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hint : eaw_InteriorSubset K a)
    (hout : oc_OutsideReachesExterior (mpl_orbitLoop K a) R) :
    exc_OffSupportReachesExterior K a := by
  refine ⟨R, hRbox, ?_⟩
  intro z hzK hzsupp
  
  have hzeven : Even (jec_rayCount z (mpl_orbitLoop K a)) := by
    by_contra hodd
    exact hzK (hint z hodd)
  have hzOut : z ∉ jec_leftRegion (mpl_orbitLoop K a) := by
    rw [jec_mem_leftRegion]; exact fun h => h hzeven
  
  obtain ⟨e, heExt, hreach⟩ := hout z hzOut
  
  have hzcompl : z ∈ ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ := hzsupp
  
  obtain ⟨heB, hindReach⟩ := kc3_inducedReachable_of_floodFill (mpl_orbitLoop K a) hzcompl hreach
  exact ⟨hzcompl, e, heExt, hindReach⟩










theorem kc3_exterior_self_inducedReachable (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    ((hypercubicLattice 2).induce
        ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable
      ⟨z, exterior_subset_compl _ R hR hz⟩ ⟨z, exterior_subset_compl _ R hR hz⟩ :=
  exc_exterior_self_reachable K a R hR z hz














theorem kc3_unitCell_interiorSubset : eaw_InteriorSubset unitCell ucBase :=
  eaw_unitCell_interiorSubset




theorem kc3_unitCell_loopSupportBox :
    ∃ R : ℕ, ({z | z ∈ (mpl_orbitLoop unitCell ucBase).support} : Set (Site 2)) ⊆ box 2 R :=
  exc_exists_loopSupportBox unitCell ucBase

end Walls

end StatMech
