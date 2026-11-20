/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.OrbitWindingWitness
import Code.Lattice.BdEdgeMatchStarHull
import Code.Lattice.BdEdgeMatchClose
import Code.Lattice.ClosedContourSeparation
import Code.Lattice.EnclosedAreaWitness
import Code.Lattice.WindingEarInduction
import Code.Lattice.ExteriorConnected
import Code.Lattice.ExteriorConnectedDischarge
import Code.Lattice.LexMinOrientation
import Code.Lattice.LeftFenceAnchor
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.StarHullFinite
import Code.Lattice.StarHullWinding

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

















theorem kc_backwardHalf {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2}
    (hflip : u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) :
    bdEdge (jec_leftRegion Vc) s(u, v) := by
  rw [bdEdge_mk]; exact hflip









theorem kc_windingBoundary_iff_support_flip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔
      ((u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) ∧
        (u ∈ Vc.support ∨ v ∈ Vc.support)) :=
  bemc_bdEdge_iff_support_flip Vc hadj















theorem kc_leftRegion_eq_of_rayParity {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc))
    (hout : ∀ z, z ∉ K → Even (jec_rayCount z Vc)) :
    K = jec_leftRegion Vc :=
  ccs_cluster_eq_leftRegion Vc hin hout








theorem kc_bdEdgeMatch_of_rayParity {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc))
    (hout : ∀ z, z ∉ K → Even (jec_rayCount z Vc)) :
    pww_BdEdgeMatch K Vc :=
  pbs_bdEdgeMatch_of_leftRegion_eq Vc (kc_leftRegion_eq_of_rayParity Vc hin hout)













theorem kc_exteriorEven_iff_interiorSubset (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    eaw_InteriorSubset K a ↔
      (∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a))) := by
  unfold eaw_InteriorSubset
  constructor
  · intro h z hz
    by_contra hodd
    exact hz (h z hodd)
  · intro h z hodd
    by_contra hz
    exact hodd (h z hz)



theorem kc_exteriorEven_of_interiorSubset (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hint : eaw_InteriorSubset K a) :
    ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a)) :=
  (kc_exteriorEven_iff_interiorSubset K a).mp hint
















theorem kc_rayParity_in_of_windingWitness (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hw : wei_WindingWitness K a)
    (hInt : ∀ z₀, z₀ ∈ K → ∀ z, z ∈ K →
      ∃ p : (hypercubicLattice 2).Walk z z₀,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
    ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  obtain ⟨z₀, hz₀K, hz₀odd⟩ := hw
  exact wei_insideHalf_of_windingWitness K a hz₀K hz₀odd (hInt z₀ hz₀K)
























theorem kc_core_of_interiorSubset (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hw : wei_WindingWitness K a)
    (hInt : ∀ z₀, z₀ ∈ K → ∀ z, z ∈ K →
      ∃ p : (hypercubicLattice 2).Walk z z₀,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support))
    (hint : eaw_InteriorSubset K a) :
    pww_BdEdgeMatch K (mpl_orbitLoop K a) :=
  kc_bdEdgeMatch_of_rayParity (mpl_orbitLoop K a)
    (kc_rayParity_in_of_windingWitness K a hw hInt)
    (kc_exteriorEven_of_interiorSubset K a hint)





theorem kc_core_leftRegion_eq (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hw : wei_WindingWitness K a)
    (hInt : ∀ z₀, z₀ ∈ K → ∀ z, z ∈ K →
      ∃ p : (hypercubicLattice 2).Walk z z₀,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support))
    (hint : eaw_InteriorSubset K a) :
    K = jec_leftRegion (mpl_orbitLoop K a) :=
  kc_leftRegion_eq_of_rayParity (mpl_orbitLoop K a)
    (kc_rayParity_in_of_windingWitness K a hw hInt)
    (kc_exteriorEven_of_interiorSubset K a hint)













theorem kc_core_crossedEdge_backwardHalf (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hw : wei_WindingWitness K a)
    (hInt : ∀ z₀, z₀ ∈ K → ∀ z, z ∈ K →
      ∃ p : (hypercubicLattice 2).Walk z z₀,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support))
    (hint : eaw_InteriorSubset K a) {f g : Site 2}
    (hedge : s(f, g) ∈ (mpl_orbitLoop K a).edges) :
    bdEdge (jec_leftRegion (mpl_orbitLoop K a)) (sharedPrimalEdge f g) := by
  have hbdK : bdEdge K (sharedPrimalEdge f g) := mpl_orbitLoop_edges_bdEdge K a hedge
  rwa [kc_core_leftRegion_eq K a hw hInt hint] at hbdK






















theorem kc_core_leftFence_of_interiorSubset (K : Set (Site 2)) (hK : K.Finite) (z₀ : Site 2)
    (hbd : IsBoundaryDart K (lmo_leftDartAt z₀)) (m : ℤ) (hm : z₀ 0 = m)
    (hmin : ∀ w ∈ K, m ≤ w 0)
    (hcyc : (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).IsCycle)
    (hInt : ∀ z₀', z₀' ∈ K → ∀ z, z ∈ K →
      ∃ p : (hypercubicLattice 2).Walk z z₀',
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).support))
    (hint : eaw_InteriorSubset K ⟨lmo_leftDartAt z₀, hbd⟩) :
    pww_BdEdgeMatch K (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩) :=
  kc_core_of_interiorSubset K ⟨lmo_leftDartAt z₀, hbd⟩
    (lfa_leftFence_windingWitness K hK z₀ hbd m hm hmin hcyc) hInt hint
















theorem kc_core_starHull_of_interiorSubset (K : Set (Site 2)) (hK : K.Finite) (z₀ : Site 2)
    (hbd : IsBoundaryDart (ndt_StarHull K) (lmo_leftDartAt z₀)) (m : ℤ) (hm : z₀ 0 = m)
    (hmin : ∀ w ∈ ndt_StarHull K, m ≤ w 0)
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩)
    (hInt : ∀ z₀', z₀' ∈ ndt_StarHull K → ∀ z, z ∈ ndt_StarHull K →
      ∃ p : (hypercubicLattice 2).Walk z z₀',
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩).support))
    (hint : eaw_InteriorSubset (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩) :
    pww_BdEdgeMatch (ndt_StarHull K) (mpl_orbitLoop (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩) :=
  kc_core_leftFence_of_interiorSubset (ndt_StarHull K) (starHull_finite K hK) z₀ hbd m hm hmin
    (shw_starHull_mpl_isCycle K ⟨lmo_leftDartAt z₀, hbd⟩ hp) hInt hint

























theorem kc_core_of_exc (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hw : wei_WindingWitness K a)
    (hInt : ∀ z₀, z₀ ∈ K → ∀ z, z ∈ K →
      ∃ p : (hypercubicLattice 2).Walk z z₀,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support))
    (hoff : exc_OffSupportReachesExterior K a) (hsupp : exc_SupportOddInK K a) :
    pww_BdEdgeMatch K (mpl_orbitLoop K a) :=
  kc_core_of_interiorSubset K a hw hInt (ecd_interiorSubset_of_exc K a hoff hsupp)







theorem kc_core_leftFence_of_exc (K : Set (Site 2)) (hK : K.Finite) (z₀ : Site 2)
    (hbd : IsBoundaryDart K (lmo_leftDartAt z₀)) (m : ℤ) (hm : z₀ 0 = m)
    (hmin : ∀ w ∈ K, m ≤ w 0)
    (hcyc : (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).IsCycle)
    (hInt : ∀ z₀', z₀' ∈ K → ∀ z, z ∈ K →
      ∃ p : (hypercubicLattice 2).Walk z z₀',
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).support))
    (hoff : exc_OffSupportReachesExterior K ⟨lmo_leftDartAt z₀, hbd⟩)
    (hsupp : exc_SupportOddInK K ⟨lmo_leftDartAt z₀, hbd⟩) :
    pww_BdEdgeMatch K (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩) :=
  kc_core_of_exc K ⟨lmo_leftDartAt z₀, hbd⟩
    (lfa_leftFence_windingWitness K hK z₀ hbd m hm hmin hcyc) hInt hoff hsupp













theorem kc_unitCell_supportOddInK : exc_SupportOddInK unitCell ucBase :=
  exc_unitCell_supportOddInK





theorem kc_unitCell_interiorSubset : eaw_InteriorSubset unitCell ucBase :=
  eaw_unitCell_interiorSubset






theorem kc_unitCell_exteriorEven :
    ∀ z, z ∉ unitCell → Even (jec_rayCount z (mpl_orbitLoop unitCell ucBase)) :=
  kc_exteriorEven_of_interiorSubset unitCell ucBase kc_unitCell_interiorSubset

end Walls

end StatMech
