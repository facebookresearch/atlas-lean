/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Mathlib
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.JordanEnclosure
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge
import Code.Walls.jc6_singlecycle

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem jc7_orbit_isCycle (K : Set (Site 2)) (hK : K.Finite) : jc6_SingleCycle K :=
  jc6_singleCycle K hK












theorem jc7_loop_localConstancy (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (olb_orbitLoop K hK e he).support)
    (hv : v ∉ (olb_orbitLoop K hK e he).support) :
    (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔
      Even (jec_rayCount v (olb_orbitLoop K hK e he))) :=
  olb_orbit_separation K hK e he hadj hu hv















theorem jc7_loop_leftRegion_bdEdge_support (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support :=
  olb_orbit_leftRegion_bdEdge K hK e he hadj hbd
















def jc7_LoopSeparates (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : Prop :=
  (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    u ∉ (olb_orbitLoop K hK e he).support →
    v ∉ (olb_orbitLoop K hK e he).support →
    (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔
      Even (jec_rayCount v (olb_orbitLoop K hK e he)))) ∧
  (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v) →
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support)




theorem jc7_loopSeparates (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : jc7_LoopSeparates K hK e he :=
  ⟨fun hadj hu hv => jc7_loop_localConstancy K hK e he hadj hu hv,
   fun hadj hbd => jc7_loop_leftRegion_bdEdge_support K hK e he hadj hbd⟩






















end Walls

end StatMech
