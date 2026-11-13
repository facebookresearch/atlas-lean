/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.OrbitEncloses

open Set SimpleGraph Function

namespace StatMech

namespace Lattice


















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
