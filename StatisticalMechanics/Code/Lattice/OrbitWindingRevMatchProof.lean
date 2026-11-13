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
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.OrbitInteriorOdd
import Code.Lattice.ClosedContourSeparation
import Code.Lattice.OrbitWindingWitness
import Code.Lattice.BdEdgeMatchStarHull
import Code.Lattice.JordanSeparationFull
import Code.Lattice.OuterBoundarySingle
import Code.Lattice.OrbitSeparatesProof
import Code.Lattice.OrbitFillsWindingProof

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}





















theorem owr_leftRegion_subset_of_exterior (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0)) :
    jec_leftRegion (olb_orbitLoop K hK e he) ⊆ K := by
  intro z hz
  rw [jec_mem_leftRegion] at hz
  by_contra hzK
  exact hz (oee_outsideHalf_of_exteriorEq K hK e he hExt z hzK)






















theorem owr_revMatch_of_subset_and_noCross (K : Set (Site 2)) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hsub : jec_leftRegion Vc ⊆ K)
    (hnoCross : ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
      x ∈ jec_leftRegion Vc → y ∈ K → y ∈ jec_leftRegion Vc) :
    ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
      bdEdge (jec_leftRegion Vc) s(x, y) → bdEdge K s(x, y) := by
  intro x y hadj hbd
  rw [bdEdge_mk] at hbd ⊢
  by_cases hxL : x ∈ jec_leftRegion Vc
  · 
    have hyL : y ∉ jec_leftRegion Vc := hbd.mp hxL
    have hxK : x ∈ K := hsub hxL
    exact ⟨fun _ hyK => hyL (hnoCross x y hadj hxL hyK), fun _ => hxK⟩
  · 
    have hyL : y ∈ jec_leftRegion Vc := by
      by_contra hyL; exact hxL (hbd.mpr hyL)
    have hyK : y ∈ K := hsub hyL
    have hxK : x ∉ K := fun hxK => hxL (hnoCross y x hadj.symm hyL hxK)
    exact ⟨fun hxK' => absurd hxK' hxK, fun hyK' => absurd hyK hyK'⟩











theorem owr_noCross_of_interior (K : Set (Site 2)) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hKsub : K ⊆ jec_leftRegion Vc) :
    ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
      x ∈ jec_leftRegion Vc → y ∈ K → y ∈ jec_leftRegion Vc :=
  fun _ _ _ _ hyK => hKsub hyK






theorem owr_revMatch_of_inclusions (K : Set (Site 2)) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hsub : jec_leftRegion Vc ⊆ K) (hKsub : K ⊆ jec_leftRegion Vc) :
    ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
      bdEdge (jec_leftRegion Vc) s(x, y) → bdEdge K s(x, y) :=
  owr_revMatch_of_subset_and_noCross K Vc hsub (owr_noCross_of_interior K Vc hKsub)
























theorem owr_revMatch_of_winding (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
    {z0 : Site 2} (hz0K : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)) :
    OrbitWindingRevMatch K hK e he :=
  ofw_revMatch_of_match K hK e he
    (pbs_bdEdgeMatch_of_winding K hK e he hExt hz0K hodd0 hInt)













theorem owr_revMatch_of_match (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he)) :
    OrbitWindingRevMatch K hK e he :=
  ofw_revMatch_of_match K hK e he hmatch





theorem owr_revMatch_of_interiorInclusion (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
    (hKsub : K ⊆ jec_leftRegion (olb_orbitLoop K hK e he)) :
    OrbitWindingRevMatch K hK e he :=
  fun x y hadj hbd =>
    owr_revMatch_of_inclusions K (olb_orbitLoop K hK e he)
      (owr_leftRegion_subset_of_exterior K hK e he hExt) hKsub x y hadj hbd














theorem owr_orbitSeparates_of_winding (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
    {z0 : Site 2} (hz0K : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support))
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitSeparates K e :=
  ofw_orbitSeparates_of_revMatch_cover K hK e he
    (pbs_bdEdgeMatch_of_winding K hK e he hExt hz0K hodd0 hInt) hcov






theorem owr_traceSurjective_of_winding (hfin : (cluster 2 ω (origin 2)).Finite)
    (hExt : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      ∀ z, z ∉ cluster 2 ω (origin 2) → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support) ∧
        (∀ q ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, z0 0 ≤ q 0))
    (hwit : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      ∃ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) ∧
        ¬ Even (jec_rayCount z0 (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he)) ∧
        ∀ z, z ∈ cluster 2 ω (origin 2) → ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support))
    (hcov : ∀ (e : Dart), IsBoundaryDart (cluster 2 ω (origin 2)) e →
      OrbitCoversBoundaryEdges (cluster 2 ω (origin 2)) e) :
    OrbitTraceSurjective (cluster 2 ω (origin 2)) :=
  ofw_traceSurjective_of_revMatch_cover (ω := ω) hfin
    (fun e he => by
      obtain ⟨z0, hz0K, hodd0, hInt⟩ := hwit e he
      exact pbs_bdEdgeMatch_of_winding (cluster 2 ω (origin 2)) hfin e he (hExt e he) hz0K hodd0
        hInt)
    hcov







theorem owr_pc_lt_one_of_residues_and_links
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  ofw_pc_lt_one_of_residues_and_links h

































end Lattice

end StatMech
