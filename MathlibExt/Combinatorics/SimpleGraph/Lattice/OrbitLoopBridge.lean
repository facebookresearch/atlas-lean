/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitEncloses

/-!
# Face loops of boundary orbits as lattice walks

Viewing the face loop of a boundary orbit as a closed walk in the square lattice, every closed walk
crosses any set an even number of times, and the inside of the loop in the sense of ray parity
(`jec_leftRegion`) has all its boundary edges at sites of the loop.

## Main definitions

* `StatMech.Lattice.olb_orbitLoop K hK e he`: the face loop of the orbit of `e`, as a lattice walk.

## Main results

* `StatMech.Lattice.olb_orbitLoop_edges_bdEdge`: each edge of the loop crosses the boundary of `K`.
* `StatMech.Lattice.olb_orbitLoop_crossCount_even`: the loop crosses any set an even number of
  times.
* `StatMech.Lattice.olb_orbit_leftRegion_bdEdge`: boundary edges of the inside of the loop touch the
  loop.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The face loop of the boundary orbit of `e`, as a closed walk in the square lattice. -/
noncomputable def olb_orbitLoop (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : (hypercubicLattice 2).Walk (dartFace e) (dartFace e) :=
  (dartOrbitFaceLoop K hK e he).mapLe (faceBoundaryGraph_le K)

theorem olb_orbitLoop_support (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    (olb_orbitLoop K hK e he).support = (dartOrbitFaceLoop K hK e he).support := by
  unfold olb_orbitLoop
  exact SimpleGraph.Walk.support_mapLe_eq_support _ _

theorem olb_orbitLoop_edges (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    (olb_orbitLoop K hK e he).edges = (dartOrbitFaceLoop K hK e he).edges := by
  unfold olb_orbitLoop
  exact SimpleGraph.Walk.edges_mapLe_eq_edges _ _

theorem olb_orbitLoop_length (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    (olb_orbitLoop K hK e he).length = (dartOrbitFaceLoop K hK e he).length := by
  rw [olb_orbitLoop, SimpleGraph.Walk.mapLe]
  exact (dartOrbitFaceLoop K hK e he).length_map (Hom.ofLE (faceBoundaryGraph_le K))

theorem olb_orbitLoop_length_pos (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : 0 < (olb_orbitLoop K hK e he).length := by
  rw [olb_orbitLoop_length]
  exact dartOrbitFaceLoop_length_pos K hK e he

theorem olb_orbitLoop_ne_nil (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : olb_orbitLoop K hK e he ≠ SimpleGraph.Walk.nil := by
  intro h
  have := olb_orbitLoop_length_pos K hK e he
  rw [h] at this
  simp at this

theorem olb_orbitLoop_edges_bdEdge (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {f g : Site 2}
    (h : s(f, g) ∈ (olb_orbitLoop K hK e he).edges) :
    bdEdge K (sharedPrimalEdge f g) := by
  rw [olb_orbitLoop_edges] at h
  exact dartOrbitFaceLoop_edges_bdEdge K hK e he h

theorem olb_orbitLoop_crossCount_even (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (S : Set (Site 2)) :
    Even (crossCount S (olb_orbitLoop K hK e he)) :=
  crossCount_even_of_loop S (olb_orbitLoop K hK e he)

theorem olb_orbit_separation (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (olb_orbitLoop K hK e he).support)
    (hv : v ∉ (olb_orbitLoop K hK e he).support) :
    (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔
      Even (jec_rayCount v (olb_orbitLoop K hK e he))) :=
  jec_localConstancy (olb_orbitLoop K hK e he) hadj hu hv

theorem olb_orbit_leftRegion_bdEdge (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support :=
  jec_leftRegion_bdEdge_support (olb_orbitLoop K hK e he) hadj hbd

end Lattice

end StatMech
