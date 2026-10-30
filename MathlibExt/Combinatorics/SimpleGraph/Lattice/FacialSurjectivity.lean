/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.RotationSystemFaces

/-!
# Boundary-dart sets of the components off a closed walk

Let `Vc` be a closed walk in the square lattice. Each connected component of the sites off its
support has a nonempty set of boundary darts, and distinct components have distinct sets, so the
components are counted by the family of these dart sets (`fsv_canonicalFamily`). If every component
`C` has a single boundary orbit (`fsv_RegionSingleFace C`), the family is the family of boundary
orbits of the components, and the components are counted by these orbits.

## Main definitions

* `StatMech.Lattice.fsv_canonicalFamily Vc`: the sets of boundary darts of the components off the
  support of `Vc`.
* `StatMech.Lattice.fsv_RegionSingleFace C`: all boundary darts of `C` lie in one orbit of
  `dartNext C`.
* `StatMech.Lattice.fsv_singleOrbitFamily Vc`: the boundary orbits of the components off the support
  of `Vc`.

## Main results

* `StatMech.Lattice.fsv_componentCount_eq_canonicalCount`: the number of components off `Vc` equals
  the number of their boundary-dart sets.
* `StatMech.Lattice.fsv_boundaryDartSet_eq_orbit`: if every boundary dart lies in the orbit of `e`,
  the boundary-dart set is that orbit.
* `StatMech.Lattice.fsv_componentCount_eq_singleOrbitCount`: if every component has a single
  boundary orbit, the number of components equals the number of these orbits.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The family of boundary-dart sets of the connected components of the sites off the support of the
closed walk `Vc`: one set for each component. -/
def fsv_canonicalFamily {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Set (Set Dart) :=
  {D | ∃ z : Site 2, z ∉ Vc.support ∧
    D = {e : Dart | IsBoundaryDart (offSupportComponent Vc z) e}}

/-- The canonical family is the range of the map sending a component off `Vc` to its boundary
darts. -/
theorem fsv_range_eq_canonical {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    Set.range (rsf_componentDarts Vc) = fsv_canonicalFamily Vc := by
  ext D
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨v, rfl⟩ := c.exists_rep
    exact ⟨v.1, v.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(fcb_offComplGraph Vc).connectedComponentMk ⟨z, hz⟩, rfl⟩

/-- The canonical family satisfies `rsf_FacialOrbitsCoverComponents`. -/
theorem fsv_facialOrbitsCoverComponents_canonical {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    rsf_FacialOrbitsCoverComponents Vc (fsv_canonicalFamily Vc) :=
  fsv_range_eq_canonical Vc

/-- The number of connected components off the support of `Vc` equals the number of their
boundary-dart sets. -/
theorem fsv_componentCount_eq_canonicalCount {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent
      = Nat.card (fsv_canonicalFamily Vc) :=
  rsf_componentCount_eq_facialOrbitCount Vc (fsv_facialOrbitsCoverComponents_canonical Vc)

/-- The orbit of a boundary dart under `dartNext C` consists of boundary darts of `C`. -/
theorem fsv_orbit_subset_boundaryDartSet (C : Set (Site 2)) {e : Dart}
    (he : IsBoundaryDart C e) :
    {d : Dart | SameOrbit C e d} ⊆ {d : Dart | IsBoundaryDart C d} := by
  rintro d ⟨n, rfl⟩
  exact iterate_isBoundaryDart C _ he n

/-- Every member of the canonical family is nonempty: each component off `Vc` has a boundary
dart. -/
theorem fsv_canonicalFamily_nonempty {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {D : Set Dart} (hD : D ∈ fsv_canonicalFamily Vc) : D.Nonempty := by
  obtain ⟨z, hz, rfl⟩ := hD
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc hz
  exact ⟨e, he⟩

/-- If every boundary dart of `C` lies in the orbit of the boundary dart `e`, the set of boundary
darts of `C` is that orbit. -/
theorem fsv_boundaryDartSet_eq_orbit (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e)
    (hsat : ∀ d : Dart, IsBoundaryDart C d → SameOrbit C e d) :
    {d : Dart | IsBoundaryDart C d} = {d : Dart | SameOrbit C e d} := by
  ext d
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hd; exact hsat d hd
  · rintro ⟨n, rfl⟩; exact iterate_isBoundaryDart C _ he n

/-- Under `InterfaceConnected C`, if the head of every boundary dart of `C` is connected in `Cᶜ` to
the head of `e`, every boundary dart of `C` lies in the orbit of `e`. -/
theorem fsv_hsat_of_interfaceConnected (C : Set (Site 2)) (hIC : InterfaceConnected C)
    {e : Dart} (he : IsBoundaryDart C e)
    (hheads : ∀ d : Dart, (hd : IsBoundaryDart C d) →
      ((hypercubicLattice 2).induce Cᶜ).Reachable ⟨e.head, he.2⟩ ⟨d.head, hd.2⟩) :
    ∀ d : Dart, IsBoundaryDart C d → SameOrbit C e d :=
  fun d hd => hIC e d he hd (hheads d hd)

/-- For a component `C` off `Vc` satisfying `InterfaceConnected`, if all heads of boundary darts of
`C` are connected in `Cᶜ` to the head of `e`, the boundary darts of `C` form the orbit of `e`. -/
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

/-- All boundary darts of `C` lie in a single orbit of `dartNext C`: from any boundary dart, the
orbit is the whole set of boundary darts. -/
def fsv_RegionSingleFace (C : Set (Site 2)) : Prop :=
  ∀ e : Dart, IsBoundaryDart C e →
    {d : Dart | IsBoundaryDart C d} = {d : Dart | SameOrbit C e d}

/-- The family of orbits of boundary darts of the connected components off the support of `Vc`. -/
def fsv_singleOrbitFamily {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Set (Set Dart) :=
  {D | ∃ z : Site 2, z ∉ Vc.support ∧ ∃ e : Dart, IsBoundaryDart (offSupportComponent Vc z) e ∧
    D = {d : Dart | SameOrbit (offSupportComponent Vc z) e d}}

/-- A single site has a single boundary orbit. -/
theorem fsv_RegionSingleFace_singleton (c : Site 2) :
    fsv_RegionSingleFace ({c} : Set (Site 2)) :=
  fun e he => fsv_boundaryDartSet_eq_orbit ({c} : Set (Site 2)) he
    (fun d hd => ifc_singleton_sameOrbit c e d he hd)

/-- If every component off `Vc` has a single boundary orbit, the canonical family equals the family
of boundary orbits. -/
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

/-- If every component off `Vc` has a single boundary orbit, the family of boundary orbits satisfies
`rsf_FacialOrbitsCoverComponents`. -/
theorem fsv_facialOrbitsCoverComponents_singleOrbit {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
    rsf_FacialOrbitsCoverComponents Vc (fsv_singleOrbitFamily Vc) := by
  unfold rsf_FacialOrbitsCoverComponents
  rw [fsv_range_eq_canonical, fsv_canonical_eq_singleOrbit Vc hres]

/-- If every component off the support of `Vc` has a single boundary orbit, the number of components
equals the number of boundary orbits of the components. The hypothesis `fsv_RegionSingleFace` is
proved here only for single sites (`fsv_RegionSingleFace_singleton`); no closed walk is shown to
satisfy it for all of its components. -/
theorem fsv_componentCount_eq_singleOrbitCount {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent
      = Nat.card (fsv_singleOrbitFamily Vc) :=
  rsf_componentCount_eq_facialOrbitCount Vc (fsv_facialOrbitsCoverComponents_singleOrbit Vc hres)

end Lattice

end StatMech
