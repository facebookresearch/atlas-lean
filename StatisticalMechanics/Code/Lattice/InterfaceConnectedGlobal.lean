/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.InterfaceOrbit
import Code.Lattice.InterfaceConnected
import Code.Lattice.InterfaceConnectedProof
import Code.Lattice.KingFacts

open SimpleGraph Function

namespace StatMech

namespace Lattice












theorem ifg_dartNext_head_kingReachable (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    (boundaryKingGraph K).Reachable
      ⟨e.head, he.2⟩ ⟨(dartNext K e).head, (dartNext_isBoundaryDart K e he).2⟩ := by
  rcases kf_dartNext_head_kingAdj_or_eq K e with hfix | hking
  · 
    have hsub : (⟨(dartNext K e).head, (dartNext_isBoundaryDart K e he).2⟩ : ↥(Kᶜ : Set (Site 2)))
        = ⟨e.head, he.2⟩ := Subtype.ext hfix
    rw [hsub]
  · 
    exact (((boundaryKingGraph_adj K _ _).mpr hking)).reachable




theorem ifg_iterate_head_kingReachable (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) :
    (boundaryKingGraph K).Reachable
      ⟨e.head, he.2⟩ ⟨((dartNext K)^[n] e).head, (iterate_isBoundaryDart' K e he n).2⟩ := by
  induction n with
  | zero => exact Reachable.refl _
  | succ m ih =>
    have hbd := iterate_isBoundaryDart' K e he m
    have hstep := ifg_dartNext_head_kingReachable K ((dartNext K)^[m] e) hbd
    have htrans := ih.trans hstep
    
    have hval : (dartNext K ((dartNext K)^[m] e)).head = ((dartNext K)^[m + 1] e).head := by
      rw [Function.iterate_succ_apply']
    have hsub :
        (⟨(dartNext K ((dartNext K)^[m] e)).head,
            (dartNext_isBoundaryDart K ((dartNext K)^[m] e) hbd).2⟩ : ↥(Kᶜ : Set (Site 2)))
          = ⟨((dartNext K)^[m + 1] e).head, (iterate_isBoundaryDart' K e he (m + 1)).2⟩ :=
      Subtype.ext hval
    rwa [hsub] at htrans






theorem ifg_orbit_kingReachable (K : Set (Site 2)) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f) (h : SameOrbit K e f) :
    (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
  obtain ⟨n, hn⟩ := h
  have hr := ifg_iterate_head_kingReachable K e he n
  have hval : ((dartNext K)^[n] e).head = f.head := by rw [hn]
  have hsub : (⟨((dartNext K)^[n] e).head, (iterate_isBoundaryDart' K e he n).2⟩
      : ↥(Kᶜ : Set (Site 2))) = ⟨f.head, hf.2⟩ := Subtype.ext hval
  rwa [hsub] at hr




















def OrbitTraceSurjective (K : Set (Site 2)) : Prop :=
  ∀ (e f : Dart) (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f),
    ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ →
    SameOrbit K e f



theorem orbitTraceSurjective_iff_interfaceConnected (K : Set (Site 2)) :
    OrbitTraceSurjective K ↔ InterfaceConnected K := Iff.rfl



theorem ifg_orbitTraceSurjective_singleton (c : Site 2) :
    OrbitTraceSurjective ({c} : Set (Site 2)) :=
  ifc_interfaceConnected c
















theorem ifg_boundaryKingConnected_of_clusterConnected (K : Set (Site 2))
    (hsurj : OrbitTraceSurjective K) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f)
    (hcomp : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩) :
    SameOrbit K e f ∧
      (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
  have horbit : SameOrbit K e f := hsurj e f he hf hcomp
  exact ⟨horbit, ifg_orbit_kingReachable K he hf horbit⟩















theorem ifg_no_facingDart_singleton (c v : Site 2) (hv : unitWt (v - c) ≠ 1)
    (d : Dart) (hd : IsBoundaryDart ({c} : Set (Site 2)) d) : d.head ≠ v := by
  intro hhead
  apply hv
  have htail : d.tail = c := by simpa using hd.1
  have : d.dir = v - c := by rw [Dart.dir_def, hhead, htail]
  rw [← this]; exact unitWt_dir d



theorem ifg_not_orbitReached_two_zero (e : Dart) :
    ¬ OrbitReached ({(0 : Site 2)} : Set (Site 2)) e (![2, 0] : Site 2) := by
  rintro ⟨d, hd, hdh, _⟩
  have hwt : unitWt ((![2, 0] : Site 2) - (0 : Site 2)) ≠ 1 := by
    simp only [sub_zero, unitWt, Fin.sum_univ_two]
    decide
  exact ifg_no_facingDart_singleton (0 : Site 2) (![2, 0] : Site 2) hwt d hd hdh









theorem ifg_not_orbitKingTransport_singleton :
    ¬ OrbitKingTransport ({(0 : Site 2)} : Set (Site 2)) := by
  intro htr
  
  have hg : unitWt (![1, 0] : Site 2) = 1 := by simp only [unitWt, Fin.sum_univ_two]; decide
  set e : Dart := mkDart (0 : Site 2) (![1, 0] : Site 2) hg with he_def
  have hhead : e.head = (![1, 0] : Site 2) := by rw [he_def, mkDart_head]; simp
  have htail : e.tail = (0 : Site 2) := by rw [he_def, mkDart_tail]
  have hbd : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e := by
    refine ⟨?_, ?_⟩
    · rw [htail]; exact Set.mem_singleton _
    · rw [hhead]; intro hc
      simp only [Set.mem_singleton_iff] at hc
      have := congrFun hc 0; simp at this
  
  have hou : OrbitReached ({(0 : Site 2)} : Set (Site 2)) e (![1, 0] : Site 2) := by
    have := orbitReached_self ({(0 : Site 2)} : Set (Site 2)) e hbd
    rwa [hhead] at this
  
  have hu : (![1, 0] : Site 2) ∉ ({(0 : Site 2)} : Set (Site 2)) := by
    intro hc; simp only [Set.mem_singleton_iff] at hc; have := congrFun hc 0; simp at this
  have hv : (![2, 0] : Site 2) ∉ ({(0 : Site 2)} : Set (Site 2)) := by
    intro hc; simp only [Set.mem_singleton_iff] at hc; have := congrFun hc 0; simp at this
  have hking : KingAdj (![1, 0] : Site 2) (![2, 0] : Site 2) := by
    refine ⟨?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp at this
    · intro i; fin_cases i <;> simp
  
  exact ifg_not_orbitReached_two_zero e (htr e hbd hu hv hking hou)

end Lattice

end StatMech
