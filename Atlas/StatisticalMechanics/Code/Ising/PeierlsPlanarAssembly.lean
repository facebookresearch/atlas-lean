/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Ising.OuterContourWindingClose
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.PeierlsBoundaryConnected

open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal

namespace StatMech

namespace Ising

open StatMech.Lattice
open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable









































def PlanarConnectivity (n : ℕ) : Prop :=
  ∀ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false →
    ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster K ∧
      ContourEvent (↑K : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) τ) ∧
      ∃ (T : Finset (Site 2)) (j : ℕ),
        (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
        T.Nonempty ∧
        (∀ f ∈ T, ∀ g ∈ T,
          ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f g, ∀ v ∈ p.support, v ∈ T) ∧
        j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧
        axisVertex 2 j ∈ T

















theorem outerContourFill_of_planarConnectivity (n : ℕ) (h : PlanarConnectivity n) :
    OuterContourFill n := by
  intro τ ho
  obtain ⟨K, hKbox, hKconn, hev, T, j, hsupp, hTne, hwalk, hj, hax⟩ := h τ ho
  
  have hconn : FaceBoundaryConnected (↑K : Set (Site 2)) T :=
    faceBoundaryConnected_of_walks hTne hwalk
  exact ⟨K, hKbox, hKconn, hev, T, j, hsupp, hconn, hj, hax⟩































theorem peierls_long_range_order_of_planarConnectivity
    (hConn : ∀ n : ℕ, PlanarConnectivity n) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_outerFill
    (fun n => outerContourFill_of_planarConnectivity n (hConn n))























theorem twoComponentCount_of_offSupport_connected {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    (hOutOff : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  jlri_two_components_of_offSupport_connected Vc hp hq hInOff hOutOff

















theorem walk_of_induce_walk {V : Type*} (G : SimpleGraph V) (s : Set V)
    {a b : (s : Set V)} (pInd : (G.induce s).Walk a b) :
    ∃ p : G.Walk (a : V) (b : V), ∀ v ∈ p.support, v ∈ s := by
  induction pInd with
  | @nil u =>
      refine ⟨SimpleGraph.Walk.nil, fun v hv => ?_⟩
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      subst hv; exact u.2
  | @cons x y z hadj q ih =>
    obtain ⟨p, hp⟩ := ih
    have hadj' : G.Adj (x : V) (y : V) := hadj
    refine ⟨SimpleGraph.Walk.cons hadj' p, ?_⟩
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with h | h
    · subst h; exact x.2
    · exact hp v h







theorem singletonOrigin_planarConnectivity_walks :
    singletonBoundarySupport.Nonempty ∧
      (∀ f ∈ singletonBoundarySupport, ∀ g ∈ singletonBoundarySupport,
        ∃ p : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk f g,
          ∀ v ∈ p.support, v ∈ singletonBoundarySupport) := by
  classical
  
  have hconn : ((faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).induce
      (↑singletonBoundarySupport : Set (Site 2))).Connected :=
    singletonOrigin_faceBoundaryConnected
  have hne : singletonBoundarySupport.Nonempty :=
    ⟨_, mem_singletonBoundarySupport_00⟩
  refine ⟨hne, fun f hf g hg => ?_⟩
  
  have hfs : f ∈ (↑singletonBoundarySupport : Set (Site 2)) := Finset.mem_coe.mpr hf
  have hgs : g ∈ (↑singletonBoundarySupport : Set (Site 2)) := Finset.mem_coe.mpr hg
  have hreach := hconn.preconnected
    (⟨f, hfs⟩ : (↑singletonBoundarySupport : Set (Site 2))) ⟨g, hgs⟩
  obtain ⟨pInd⟩ := hreach
  
  obtain ⟨p, hp⟩ := walk_of_induce_walk
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2)))
    (↑singletonBoundarySupport : Set (Site 2)) pInd
  refine ⟨p, fun v hv => ?_⟩
  exact Finset.mem_coe.mp (hp v hv)














theorem planarConnectivity_nonvacuous (n : ℕ) :
    ∃ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false ∧
      (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 n ∧
      IsConnectedCluster ({origin 2} : Finset (Site 2)) ∧
      ContourEvent (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n)
        (glue (plusField 2) τ) ∧
      ∃ (T : Finset (Site 2)) (j : ℕ),
        (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support
          ⊆ (T : Set (Site 2)) ∧
        T.Nonempty ∧
        (∀ f ∈ T, ∀ g ∈ T,
          ∃ p : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk f g,
            ∀ v ∈ p.support, v ∈ T) ∧
        j < contourLen (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) ∧
        axisVertex 2 j ∈ T := by
  obtain ⟨hbox, hconn, hsupp, _hfbc, hlen, hax⟩ := singletonOrigin_outerContourFill_data n
  obtain ⟨hne, hwalk⟩ := singletonOrigin_planarConnectivity_walks
  exact ⟨isoOriginCompletion n, isoOriginCompletion_origin_false n, hbox, hconn,
    singletonOrigin_contourEvent_iso n, singletonBoundarySupport, 0, hsupp, hne, hwalk, hlen, hax⟩





theorem planarConnectivity_isoOrigin (n : ℕ) :
    glue (plusField 2) (isoOriginCompletion n) (origin 2) = false →
      ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster K ∧
        ContourEvent (↑K : Set (Site 2)) (bondFinsetTouch 2 n)
          (glue (plusField 2) (isoOriginCompletion n)) ∧
        ∃ (T : Finset (Site 2)) (j : ℕ),
          (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
          T.Nonempty ∧
          (∀ f ∈ T, ∀ g ∈ T,
            ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f g, ∀ v ∈ p.support, v ∈ T) ∧
          j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧
          axisVertex 2 j ∈ T := by
  intro _ho
  obtain ⟨hbox, hconn, hsupp, _hfbc, hlen, hax⟩ := singletonOrigin_outerContourFill_data n
  obtain ⟨hne, hwalk⟩ := singletonOrigin_planarConnectivity_walks
  exact ⟨({origin 2} : Finset (Site 2)), hbox, hconn,
    singletonOrigin_contourEvent_iso n, singletonBoundarySupport, 0, hsupp, hne, hwalk, hlen, hax⟩

end Ising

end StatMech
