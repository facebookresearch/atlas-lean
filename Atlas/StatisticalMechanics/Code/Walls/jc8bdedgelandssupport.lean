/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Mathlib
import Code.Lattice.JordanEnclosure
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitLoopBridge
import Code.Walls.jc7loopseparates

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice












theorem jc8_loop_localConstancy (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (olb_orbitLoop K hK e he).support)
    (hv : v ∉ (olb_orbitLoop K hK e he).support) :
    (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔
      Even (jec_rayCount v (olb_orbitLoop K hK e he))) :=
  jc7_loop_localConstancy K hK e he hadj hu hv




















theorem jc8_bdEdge_lands_support (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hu, hv⟩ := hcon
  
  rw [bdEdge_mk] at hbd
  simp only [jec_mem_leftRegion] at hbd
  
  have hpar := jc8_loop_localConstancy K hK e he hadj hu hv
  
  tauto







theorem jc8_bdEdge_lands_support' (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support :=
  jc7_loop_leftRegion_bdEdge_support K hK e he hadj hbd






def jc8_BdEdgeLandsSupport (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : Prop :=
  ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v) →
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support




theorem jc8_bdEdgeLandsSupport (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : jc8_BdEdgeLandsSupport K hK e he :=
  fun hadj hbd => jc8_bdEdge_lands_support K hK e he hadj hbd























end Walls

end StatMech
