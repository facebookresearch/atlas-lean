/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanContour
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.InsideConnected
import Code.Lattice.OutsideConnected
import Code.Lattice.MinimalPeriodLoop

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}















noncomputable def icc_offComplGraph (Vc : (hypercubicLattice 2).Walk a a) :
    SimpleGraph {z : Site 2 // z ∉ Vc.support} :=
  (offSupport Vc).induce {z : Site 2 | z ∉ Vc.support}

@[simp] theorem icc_offComplGraph_adj (Vc : (hypercubicLattice 2).Walk a a)
    (x y : {z : Site 2 // z ∉ Vc.support}) :
    (icc_offComplGraph Vc).Adj x y ↔ (offSupport Vc).Adj (x : Site 2) (y : Site 2) :=
  Iff.rfl




theorem icc_induce_reachable_to_ambient (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}} (h : (icc_offComplGraph Vc).Reachable x y) :
    (offSupport Vc).Reachable (x : Site 2) (y : Site 2) := by
  obtain ⟨w⟩ := h
  have hle : icc_offComplGraph Vc ≤
      (offSupport Vc).comap (Function.Embedding.subtype _) := fun u v huv => huv
  exact ⟨(w.mapLe hle).map (SimpleGraph.Hom.comap (Function.Embedding.subtype _) (offSupport Vc))⟩




theorem icc_ambient_reachable_to_induce (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}}
    (h : (offSupport Vc).Reachable (x : Site 2) (y : Site 2)) :
    (icc_offComplGraph Vc).Reachable x y := by
  obtain ⟨pw, hpw⟩ := offSupport_reachable_to_offSupportWalk Vc h x.2
  obtain ⟨w⟩ := offSupportWalk_to_offSupport_reachable Vc pw hpw
  have hwoff : ∀ z ∈ w.support, z ∈ {z : Site 2 | z ∉ Vc.support} :=
    fun z hz => offSupport_walk_support_offSupport Vc w x.2 z hz
  exact walk_induce_reachable (offSupport Vc) {z : Site 2 | z ∉ Vc.support} w hwoff x.2 y.2




theorem icc_induce_reachable_iff (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}} :
    (icc_offComplGraph Vc).Reachable x y ↔ (offSupport Vc).Reachable (x : Site 2) (y : Site 2) :=
  ⟨icc_induce_reachable_to_ambient Vc, icc_ambient_reachable_to_induce Vc⟩




theorem icc_mem_offSupportComponent_iff (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}} :
    (icc_offComplGraph Vc).connectedComponentMk x = (icc_offComplGraph Vc).connectedComponentMk y ↔
      (y : Site 2) ∈ offSupportComponent Vc (x : Site 2) := by
  rw [ConnectedComponent.eq, icc_induce_reachable_iff, mem_offSupportComponent]











theorem icc_card_two_dichotomy {α : Type*} (h : Nat.card α = 2) {a b : α} (hab : a ≠ b) (c : α) :
    c = a ∨ c = b := by
  classical
  have hfin : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype α := Fintype.ofFinite α
  by_contra hc
  push Not at hc
  obtain ⟨hca, hcb⟩ := hc
  have h3 : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hcb.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hab, hca.symm⟩
  have hle : ({a, b, c} : Finset α).card ≤ Fintype.card α := Finset.card_le_univ _
  rw [Nat.card_eq_fintype_card] at h
  omega



theorem icc_card_two_dichotomy_nonvacuous (c : Bool) : c = true ∨ c = false := by
  cases c <;> simp






theorem icc_components_distinct (Vc : (hypercubicLattice 2).Walk a a)
    {sIn sOut : {z : Site 2 // z ∉ Vc.support}}
    (hInMem : (sIn : Site 2) ∈ jec_leftRegion Vc) (hOutMem : (sOut : Site 2) ∉ jec_leftRegion Vc) :
    (icc_offComplGraph Vc).connectedComponentMk sIn ≠
      (icc_offComplGraph Vc).connectedComponentMk sOut := by
  rw [Ne, ConnectedComponent.eq, icc_induce_reachable_iff]
  intro hreach
  exact hOutMem (offSupport_component_monochromatic Vc hInMem hreach sIn.2)





















theorem icc_covers_of_two_components (Vc : (hypercubicLattice 2).Walk a a)
    (hcard : Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2)
    {sIn sOut : Site 2}
    (hInMem : sIn ∈ jec_leftRegion Vc) (hInOff : sIn ∉ Vc.support)
    (hOutMem : sOut ∉ jec_leftRegion Vc) (hOutOff : sOut ∉ Vc.support)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
    jec_leftRegion Vc ⊆ offSupportComponent Vc sIn := by
  
  set SIn : {z : Site 2 // z ∉ Vc.support} := ⟨sIn, hInOff⟩ with hSIn
  set SOut : {z : Site 2 // z ∉ Vc.support} := ⟨sOut, hOutOff⟩ with hSOut
  have hdistinct : (icc_offComplGraph Vc).connectedComponentMk SIn ≠
      (icc_offComplGraph Vc).connectedComponentMk SOut :=
    icc_components_distinct Vc hInMem hOutMem
  intro z hz
  rw [mem_offSupportComponent]
  
  have hzoff : z ∉ Vc.support := hoffIn z hz
  set Z : {z : Site 2 // z ∉ Vc.support} := ⟨z, hzoff⟩ with hZ
  
  rcases icc_card_two_dichotomy hcard hdistinct
      ((icc_offComplGraph Vc).connectedComponentMk Z) with h1 | h2
  · 
    rw [eq_comm, ConnectedComponent.eq, icc_induce_reachable_iff] at h1
    exact h1
  · 
    rw [eq_comm, ConnectedComponent.eq, icc_induce_reachable_iff] at h2
    exact absurd hz (offSupport_component_monochromatic_out Vc hOutMem h2 hOutOff)






theorem icc_interior_eq_offSupportComponent (Vc : (hypercubicLattice 2).Walk a a)
    (hcard : Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2)
    {sIn sOut : Site 2}
    (hInMem : sIn ∈ jec_leftRegion Vc) (hInOff : sIn ∉ Vc.support)
    (hOutMem : sOut ∉ jec_leftRegion Vc) (hOutOff : sOut ∉ Vc.support)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
    jec_leftRegion Vc = offSupportComponent Vc sIn :=
  (interior_eq_offSupportComponent_iff Vc hInMem hInOff).mpr
    (icc_covers_of_two_components Vc hcard hInMem hInOff hOutMem hOutOff hoffIn)











theorem icc_inside_offSupport_connected (Vc : (hypercubicLattice 2).Walk a a)
    (hcard : Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2)
    {sIn sOut : Site 2}
    (hInMem : sIn ∈ jec_leftRegion Vc) (hInOff : sIn ∉ Vc.support)
    (hOutMem : sOut ∉ jec_leftRegion Vc) (hOutOff : sOut ∉ Vc.support)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      (offSupport Vc).Reachable s t :=
  inside_offSupport_connected_of_covers Vc
    (icc_covers_of_two_components Vc hcard hInMem hInOff hOutMem hOutOff hoffIn)









theorem icc_hInOff_of_two_components (Vc : (hypercubicLattice 2).Walk a a)
    (hcard : Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2)
    {sIn sOut : Site 2}
    (hInMem : sIn ∈ jec_leftRegion Vc) (hInOff : sIn ∉ Vc.support)
    (hOutMem : sOut ∉ jec_leftRegion Vc) (hOutOff : sOut ∉ Vc.support)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support :=
  hInOff_of_covers Vc hoffIn
    (icc_covers_of_two_components Vc hcard hInMem hInOff hOutMem hOutOff hoffIn)






















theorem icc_two_components_of_count (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hcard : Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2)
    {sIn sOut : Site 2}
    (hInMem : sIn ∈ jec_leftRegion Vc) (hInOff : sIn ∉ Vc.support)
    (hOutMem : sOut ∉ jec_leftRegion Vc) (hOutOff : sOut ∉ Vc.support)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hOut : oc_OutsideReachesExterior Vc R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  oc_two_components_of_outsideReaches Vc R hsupp hp hq
    (icc_hInOff_of_two_components Vc hcard hInMem hInOff hOutMem hOutOff hoffIn)
    hOut









theorem icc_minimalLoop_covers_of_two_components (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hcard : Nat.card (icc_offComplGraph (mpl_orbitLoop K a)).ConnectedComponent = 2)
    {sIn sOut : Site 2}
    (hInMem : sIn ∈ jec_leftRegion (mpl_orbitLoop K a)) (hInOff : sIn ∉ (mpl_orbitLoop K a).support)
    (hOutMem : sOut ∉ jec_leftRegion (mpl_orbitLoop K a))
    (hOutOff : sOut ∉ (mpl_orbitLoop K a).support)
    (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support) :
    jec_leftRegion (mpl_orbitLoop K a) ⊆ offSupportComponent (mpl_orbitLoop K a) sIn :=
  icc_covers_of_two_components (mpl_orbitLoop K a) hcard hInMem hInOff hOutMem hOutOff hoffIn


theorem icc_minimalLoop_hInOff_of_two_components (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hcard : Nat.card (icc_offComplGraph (mpl_orbitLoop K a)).ConnectedComponent = 2)
    {sIn sOut : Site 2}
    (hInMem : sIn ∈ jec_leftRegion (mpl_orbitLoop K a)) (hInOff : sIn ∉ (mpl_orbitLoop K a).support)
    (hOutMem : sOut ∉ jec_leftRegion (mpl_orbitLoop K a))
    (hOutOff : sOut ∉ (mpl_orbitLoop K a).support)
    (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support) :
    ∀ s t : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) →
      t ∈ jec_leftRegion (mpl_orbitLoop K a) →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support :=
  icc_hInOff_of_two_components (mpl_orbitLoop K a) hcard hInMem hInOff hOutMem hOutOff hoffIn








theorem icc_minimalLoop_two_components_of_count (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p (mpl_orbitLoop K a)))
    (hq : ∀ w ∈ (mpl_orbitLoop K a).support, w 0 ≤ q 0 - 1)
    (hcard : Nat.card (icc_offComplGraph (mpl_orbitLoop K a)).ConnectedComponent = 2)
    {sIn sOut : Site 2}
    (hInMem : sIn ∈ jec_leftRegion (mpl_orbitLoop K a)) (hInOff : sIn ∉ (mpl_orbitLoop K a).support)
    (hOutMem : sOut ∉ jec_leftRegion (mpl_orbitLoop K a))
    (hOutOff : sOut ∉ (mpl_orbitLoop K a).support)
    (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    (hOut : oc_OutsideReachesExterior (mpl_orbitLoop K a) R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).ConnectedComponent = 2 :=
  icc_two_components_of_count (mpl_orbitLoop K a) R hsupp hp hq hcard hInMem hInOff hOutMem hOutOff
    hoffIn hOut

end Lattice

end StatMech
