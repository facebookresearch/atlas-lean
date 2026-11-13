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
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.InterfaceOrbit
import Code.Lattice.InterfaceConnected
import Code.Lattice.InterfaceConnectedProof
import Code.Lattice.InsideConnected
import Code.Lattice.FaceComponentBijection
import Code.Lattice.RotationSystemFaces

open Set SimpleGraph Function

namespace StatMech

namespace Lattice













def fsv_canonicalFamily {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Set (Set Dart) :=
  {D | ∃ z : Site 2, z ∉ Vc.support ∧
    D = {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e}}







theorem fsv_range_eq_canonical {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    Set.range (rsf_componentDarts Vc) = fsv_canonicalFamily Vc := by
  ext D
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨v, rfl⟩ := c.exists_rep
    exact ⟨v.1, v.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(fcb_offComplGraph Vc).connectedComponentMk ⟨z, hz⟩, rfl⟩







theorem fsv_facialOrbitsCoverComponents_canonical {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    rsf_FacialOrbitsCoverComponents Vc (fsv_canonicalFamily Vc) :=
  fsv_range_eq_canonical Vc






theorem fsv_componentCount_eq_canonicalCount {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent
      = Nat.card (fsv_canonicalFamily Vc) :=
  rsf_componentCount_eq_facialOrbitCount Vc (fsv_facialOrbitsCoverComponents_canonical Vc)













theorem fsv_boundaryDartSet_dartNext_closed (C : Set (Site 2)) {e : Dart}
    (he : IsBoundaryDart C e) : IsBoundaryDart C (dartNext C e) :=
  dartNext_isBoundaryDart C e he





theorem fsv_orbit_subset_boundaryDartSet (C : Set (Site 2)) {e : Dart}
    (he : IsBoundaryDart C e) :
    {d : Dart | SameOrbit C e d} ⊆ {d : Dart | IsBoundaryDart C d} := by
  rintro d ⟨n, rfl⟩
  exact rsf_orbit_isBoundaryDart C he n





theorem fsv_canonicalFamily_nonempty {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {D : Set Dart} (hD : D ∈ fsv_canonicalFamily Vc) : D.Nonempty := by
  obtain ⟨z, hz, rfl⟩ := hD
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc hz
  exact ⟨e, he⟩

















theorem fsv_boundaryDartSet_eq_orbit (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e)
    (hsat : ∀ d : Dart, IsBoundaryDart C d → SameOrbit C e d) :
    {d : Dart | IsBoundaryDart C d} = {d : Dart | SameOrbit C e d} := by
  ext d
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hd; exact hsat d hd
  · rintro ⟨n, rfl⟩; exact rsf_orbit_isBoundaryDart C he n





theorem fsv_hsat_of_interfaceConnected (C : Set (Site 2)) (hIC : InterfaceConnected C)
    {e : Dart} (he : IsBoundaryDart C e)
    (hheads : ∀ d : Dart, (hd : IsBoundaryDart C d) →
      ((hypercubicLattice 2).induce Cᶜ).Reachable ⟨e.head, he.2⟩ ⟨d.head, hd.2⟩) :
    ∀ d : Dart, IsBoundaryDart C d → SameOrbit C e d :=
  fun d hd => hIC e d he hd (hheads d hd)







theorem fsv_canonicalMember_eq_orbit_of_residues {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hIC : InterfaceConnected (offSupportComponent Vc z))
    {e : Dart} (he : IsBoundaryDart (offSupportComponent Vc z) e)
    (hheads : ∀ d : Dart, (hd : IsBoundaryDart (offSupportComponent Vc z) d) →
      ((hypercubicLattice 2).induce (offSupportComponent Vc z)ᶜ).Reachable
        ⟨e.head, he.2⟩ ⟨d.head, hd.2⟩) :
    {d : Dart | IsBoundaryDart (offSupportComponent Vc z) d}
      = {d : Dart | SameOrbit (offSupportComponent Vc z) e d} :=
  fsv_boundaryDartSet_eq_orbit (offSupportComponent Vc z) he
    (fsv_hsat_of_interfaceConnected (offSupportComponent Vc z) hIC he hheads)

















def fsv_RegionSingleFace (C : Set (Site 2)) : Prop :=
  ∀ e : Dart, IsBoundaryDart C e →
    {d : Dart | IsBoundaryDart C d} = {d : Dart | SameOrbit C e d}






def fsv_singleOrbitFamily {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Set (Set Dart) :=
  {D | ∃ z : Site 2, z ∉ Vc.support ∧ ∃ e : Dart, IsBoundaryDart (offSupportComponent Vc z) e ∧
    D = {d : Dart | SameOrbit (offSupportComponent Vc z) e d}}






theorem fsv_RegionSingleFace_singleton (c : Site 2) :
    fsv_RegionSingleFace ({c} : Set (Site 2)) :=
  fun e he => fsv_boundaryDartSet_eq_orbit ({c} : Set (Site 2)) he
    (fun d hd => ifc_singleton_sameOrbit c e d he hd)






theorem fsv_canonical_eq_singleOrbit {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
    fsv_canonicalFamily Vc = fsv_singleOrbitFamily Vc := by
  ext D
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc hz
    exact ⟨z, hz, e, he, hres z hz e he⟩
  · rintro ⟨z, hz, e, he, rfl⟩
    exact ⟨z, hz, (hres z hz e he).symm⟩








theorem fsv_facialOrbitsCoverComponents_singleOrbit {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
    rsf_FacialOrbitsCoverComponents Vc (fsv_singleOrbitFamily Vc) := by
  unfold rsf_FacialOrbitsCoverComponents
  rw [fsv_range_eq_canonical, fsv_canonical_eq_singleOrbit Vc hres]





theorem fsv_componentCount_eq_singleOrbitCount {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent
      = Nat.card (fsv_singleOrbitFamily Vc) :=
  rsf_componentCount_eq_facialOrbitCount Vc (fsv_facialOrbitsCoverComponents_singleOrbit Vc hres)

end Lattice

end StatMech
