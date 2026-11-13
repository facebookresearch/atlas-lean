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
import Code.Lattice.InterfaceConnected
import Code.Lattice.InterfaceConnectedProof
import Code.Lattice.InterfaceOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.OrbitWindingWitness
import Code.Lattice.OuterBoundarySingle
import Code.Lattice.OrbitSeparatesProof

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}








theorem ofw_orbitEdge_one_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (h : IsOrbitEdge K e x y) : (x ∈ K ↔ y ∉ K) :=
  obs_orbitEdge_one_in_K K e he h


theorem ofw_orbitEdge_bdEdge_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (h : IsOrbitEdge K e x y) : bdEdge K s(x, y) :=
  osp_orbitEdge_bdEdge K e he h














theorem ofw_localConstancy_gives_support_only (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {x y : Site 2} (hadj : (hypercubicLattice 2).Adj x y)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(x, y)) :
    x ∈ (olb_orbitLoop K hK e he).support ∨ y ∈ (olb_orbitLoop K hK e he).support :=
  olb_orbit_leftRegion_bdEdge K hK e he hadj hbd
















theorem ofw_loopFaceEdge_not_orbitEdge (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {f g : Site 2} (hf : f ∉ K) (hg : g ∉ K) : ¬ IsOrbitEdge K e f g :=
  obs_not_orbitEdge_of_both_not_in_K K e he hf hg




















def OrbitWindingRevMatch (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) :
    Prop :=
  ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
    bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(x, y) → bdEdge K s(x, y)





theorem ofw_orbitFillsWinding_of_revMatch (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hrev : OrbitWindingRevMatch K hK e he)
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitFillsWinding K hK e he := by
  intro x y hadj hbd
  have hbdK : bdEdge K s(x, y) := hrev x y hadj hbd
  exact hcov hadj hbdK




theorem ofw_revMatch_of_match (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he)) :
    OrbitWindingRevMatch K hK e he := by
  intro x y _hadj hbd
  exact (hmatch s(x, y)).mpr hbd





theorem ofw_orbitFillsWinding_iff_via_coverage (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitFillsWinding K hK e he ↔ OrbitWindingRevMatch K hK e he := by
  constructor
  · intro hF2 x y hadj hbd
    exact ofw_orbitEdge_bdEdge_K K e he (hF2 x y hadj hbd)
  · intro hrev
    exact ofw_orbitFillsWinding_of_revMatch K hK e he hrev hcov








theorem ofw_orbitWindsBdEdge_of_match (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he)) :
    OrbitWindsBdEdge K hK e he :=
  osp_orbitWindsBdEdge_of_match K hK e he hmatch











theorem ofw_orbitSeparates_of_revMatch_cover (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he))
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitSeparates K e :=
  osp_orbitSeparates_of_residues K hK e he
    (ofw_orbitWindsBdEdge_of_match K hK e he hmatch)
    (ofw_orbitFillsWinding_of_revMatch K hK e he (ofw_revMatch_of_match K hK e he hmatch) hcov)










theorem ofw_traceSurjective_of_revMatch_cover (hfin : (cluster 2 ω (origin 2)).Finite)
    (hmatch : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      pww_BdEdgeMatch (cluster 2 ω (origin 2))
        (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he))
    (hcov : ∀ (e : Dart), IsBoundaryDart (cluster 2 ω (origin 2)) e →
      OrbitCoversBoundaryEdges (cluster 2 ω (origin 2)) e) :
    OrbitTraceSurjective (cluster 2 ω (origin 2)) :=
  obs_traceSurjective_of_orbitSeparates (origin 2)
    (fun e he => ofw_orbitSeparates_of_revMatch_cover (cluster 2 ω (origin 2)) hfin e he
      (hmatch e he) (hcov e he))





theorem ofw_pc_lt_one_of_residues_and_links
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  osp_pc_lt_one_of_residues_and_links h












































end Lattice

end StatMech
