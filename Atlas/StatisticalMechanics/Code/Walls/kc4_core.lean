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
import Code.Walls.kc3_offsupportreaches
import Code.Walls.kc4_eulerone
import Code.Walls.kc4_orbitiscycle

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}














noncomputable def kc4_offSupportHom (Vc : (hypercubicLattice 2).Walk a a) :
    (hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ →g
      ffc_offSupportLattice (oc_supportSet Vc) where
  toFun := fun z => (z : Site 2)
  map_rel' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hadj
    rw [ffc_offSupportLattice_adj]
    exact ⟨hadj, by simpa [oc_supportSet] using hx, by simpa [oc_supportSet] using hy⟩



















theorem kc4_reaches_exterior_of_infiniteComponent (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hzmem : z ∈ (oc_supportSet Vc)ᶜ)
    (hinf : (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  classical
  set F := oc_supportSet Vc with hF
  set G := (hypercubicLattice 2).induce Fᶜ with hG
  have hFfin : F.Finite := Set.Finite.subset (box_finite 2 R) hsupp
  obtain ⟨C0, hC0inf, hC0uniq⟩ := unique_infinite_component (by norm_num) F hFfin
  have hzC : G.connectedComponentMk ⟨z, hzmem⟩ = C0 := hC0uniq _ hinf
  have hsub : exterior 2 R ⊆ Fᶜ := exterior_subset_compl F R hsupp
  have hbext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  set e : Site 2 := beacon 2 R with he
  have hemem : e ∈ Fᶜ := hsub hbext
  
  have heCinf : (G.connectedComponentMk ⟨e, hemem⟩).supp.Infinite := by
    have : Infinite ↥(exterior 2 R) := (exterior_infinite R (by norm_num)).to_subtype
    refine Set.infinite_of_injective_forall_mem
      (f := fun w : ↥(exterior 2 R) => (⟨(w : Site 2), hsub w.2⟩ : ↥Fᶜ)) ?_ ?_
    · intro p q hpq; exact Subtype.ext (by simpa using congrArg Subtype.val hpq)
    · intro w
      rw [ConnectedComponent.mem_supp_iff]
      exact ConnectedComponent.sound
        (exterior_reachable_compl F R (by norm_num) hsub (w : Site 2) e w.2 hbext)
  have heC : G.connectedComponentMk ⟨e, hemem⟩ = C0 := hC0uniq _ heCinf
  
  have hzeReach : G.Reachable ⟨z, hzmem⟩ ⟨e, hemem⟩ := by
    rw [← ConnectedComponent.eq, hzC, heC]
  refine ⟨e, hbext, ?_⟩
  have := hzeReach.map (kc4_offSupportHom Vc)
  simpa [kc4_offSupportHom, hG, hF] using this






theorem kc4_extComponent_infinite (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {e : Site 2} (heExt : e ∈ exterior 2 R)
    (hemem : e ∈ (oc_supportSet Vc)ᶜ) :
    (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨e, hemem⟩).supp.Infinite := by
  classical
  set F := oc_supportSet Vc with hF
  set G := (hypercubicLattice 2).induce Fᶜ with hG
  have hsub : exterior 2 R ⊆ Fᶜ := exterior_subset_compl F R hsupp
  have : Infinite ↥(exterior 2 R) := (exterior_infinite R (by norm_num)).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior 2 R) => (⟨(w : Site 2), hsub w.2⟩ : ↥Fᶜ)) ?_ ?_
  · intro p q hpq; exact Subtype.ext (by simpa using congrArg Subtype.val hpq)
  · intro w
    rw [ConnectedComponent.mem_supp_iff]
    exact ConnectedComponent.sound
      (exterior_reachable_compl F R (by norm_num) hsub (w : Site 2) e w.2 heExt)




















def kc4_OutsideInInfiniteComponent (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ (z : Site 2), z ∉ jec_leftRegion Vc →
    ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
      (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite









theorem kc4_outsideReachesExterior_of_infinite (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hres : kc4_OutsideInInfiniteComponent Vc) :
    oc_OutsideReachesExterior Vc R := by
  intro z hzOut
  obtain ⟨hzmem, hinf⟩ := hres z hzOut
  exact kc4_reaches_exterior_of_infiniteComponent Vc R hsupp hzmem hinf


















theorem kc4_infinite_of_outsideReachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hflood : oc_OutsideReachesExterior Vc R) :
    kc4_OutsideInInfiniteComponent Vc := by
  intro z hzOut
  obtain ⟨e, heExt, hreach⟩ := hflood z hzOut
  
  have hzoff : z ∉ Vc.support := by
    rcases hreach with ⟨w⟩
    cases w with
    | nil => exact oc_exterior_offSupport Vc R hsupp heExt
    | cons hadj _ => exact hadj.2.1
  have hzmem : z ∈ (oc_supportSet Vc)ᶜ := by simpa [oc_supportSet] using hzoff
  refine ⟨hzmem, ?_⟩
  
  obtain ⟨p, hp⟩ := (ffc_reachable_iff_offSupportWalk (B := oc_supportSet Vc) hzmem).mp hreach
  have hemem : e ∈ (oc_supportSet Vc)ᶜ := by
    have := hp e p.end_mem_support; simpa [oc_supportSet] using this
  have hindReach :
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).Reachable ⟨z, hzmem⟩ ⟨e, hemem⟩ :=
    walk_induce_reachable (hypercubicLattice 2) ((oc_supportSet Vc)ᶜ) p (fun w hw => hp w hw)
      hzmem hemem
  
  have hcompEq :
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩ =
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨e, hemem⟩ :=
    ConnectedComponent.sound hindReach
  rw [hcompEq]
  exact kc4_extComponent_infinite Vc R hsupp heExt hemem







theorem kc4_outsideReachesExterior_iff_infinite (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    oc_OutsideReachesExterior Vc R ↔ kc4_OutsideInInfiniteComponent Vc :=
  ⟨kc4_infinite_of_outsideReachesExterior Vc R hsupp,
   kc4_outsideReachesExterior_of_infinite Vc R hsupp⟩












theorem kc4_orbit_outsideReachesExterior_of_infinite (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hres : kc4_OutsideInInfiniteComponent (mpl_orbitLoop K a)) :
    oc_OutsideReachesExterior (mpl_orbitLoop K a) R :=
  kc4_outsideReachesExterior_of_infinite (mpl_orbitLoop K a) R hRbox hres













theorem kc4_exc_offSupportReaches_of_infinite (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hint : eaw_InteriorSubset K a)
    (hres : kc4_OutsideInInfiniteComponent (mpl_orbitLoop K a)) :
    exc_OffSupportReachesExterior K a :=
  kc3_offSupportReachesExterior_of_interiorSubset_and_outside K a R hRbox hint
    (kc4_orbit_outsideReachesExterior_of_infinite K a R hRbox hres)











theorem kc4_exterior_in_infiniteComponent (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
      (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite := by
  have hzmem : z ∈ (oc_supportSet Vc)ᶜ := by
    have := oc_exterior_offSupport Vc R hsupp hz; simpa [oc_supportSet] using this
  exact ⟨hzmem, kc4_extComponent_infinite Vc R hsupp hz hzmem⟩






theorem kc4_residue_nonvacuous (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    z ∉ jec_leftRegion Vc ∧
      ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
        (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
          ⟨z, hzmem⟩).supp.Infinite :=
  ⟨oc_exterior_outside Vc R hsupp hz, kc4_exterior_in_infiniteComponent Vc R hsupp hz⟩













theorem kc4_orbitLoop_isCycle (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    (mpl_orbitLoop K a).IsCycle :=
  kc4_OrbitIsCycle K a hp hinj






theorem kc4_contour_eulerOne {p : ℕ} (hp : 3 ≤ p) : kc4_contourEulerChar p = 1 :=
  kc4_eulerOne hp

end Walls

end StatMech
