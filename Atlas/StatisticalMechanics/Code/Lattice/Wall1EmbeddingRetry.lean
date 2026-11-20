/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.Umlaufsatz
import Code.Lattice.UmlaufsatzSingleCycle
import Code.Lattice.NoPinchDual
import Code.Lattice.NoPinchMatching

open SimpleGraph Function Set Finset

namespace StatMech

namespace Lattice














theorem emb_twoVisit_pinch (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) {i j : ℕ} (hi : i ∈ usc_visitSet K a f) (hj : j ∈ usc_visitSet K a f)
    (hij : i ≠ j) :
    dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1) ∧
      ((dartNext K)^[i] a.1).dir ≠ ((dartNext K)^[j] a.1).dir := by
  classical
  
  have hfi : dartFace ((dartNext K)^[i] a.1) = f := by
    simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range] at hi; exact hi.2
  have hfj : dartFace ((dartNext K)^[j] a.1) = f := by
    simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range] at hj; exact hj.2
  refine ⟨by rw [hfi, hfj], ?_⟩
  
  intro hdir
  exact hij (usc_dir_injOn_visitSet K a f hi hj hdir)








theorem emb_twoVisit_forces_diagTouch (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) {i j : ℕ} (hi : i ∈ usc_visitSet K a f) (hj : j ∈ usc_visitSet K a f)
    (hij : i ≠ j) :
    npd_DiagTouch K f := by
  classical
  obtain ⟨hface, hdir⟩ := emb_twoVisit_pinch K a f hi hj hij
  have hbi : IsBoundaryDart K ((dartNext K)^[i] a.1) := iterate_isBoundaryDart K a.1 a.2 i
  have hbj : IsBoundaryDart K ((dartNext K)^[j] a.1) := iterate_isBoundaryDart K a.1 a.2 j
  
  have hfi : dartFace ((dartNext K)^[i] a.1) = f := by
    simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range] at hi; exact hi.2
  have := npd_pinch_forces_diagTouch hbi hbj hface hdir
  rwa [hfi] at this














theorem emb_visit_le_one_of_noDiagTouch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npd_NoDiagTouch K) (f : Site 2) :
    (usc_visitSet K a f).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro i hi j hj
  by_contra hij
  exact h f (emb_twoVisit_forces_diagTouch K a f hi hj hij)














theorem emb_faceMultiplicityOne_of_noDiagTouch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npd_NoDiagTouch K) :
    usc_FaceMultiplicityOne K a := by
  intro f hpos
  have hle := emb_visit_le_one_of_noDiagTouch K a h f
  omega
















theorem emb_faceMultiplicityOne_of_kingSaturated (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npm_KingSaturated K) :
    usc_FaceMultiplicityOne K a :=
  emb_faceMultiplicityOne_of_noDiagTouch K a (npm_noDiagTouch_of_kingSaturated h)















theorem emb_fullUnitCell_faceMultiplicityOne
    (a : {e : Dart // IsBoundaryDart ({![0, 0], ![1, 0], ![0, 1], ![1, 1]} : Set (Site 2)) e}) :
    usc_FaceMultiplicityOne ({![0, 0], ![1, 0], ![0, 1], ![1, 1]} : Set (Site 2)) a :=
  emb_faceMultiplicityOne_of_kingSaturated _ a npm_kingSaturated_example






theorem emb_unitCell_faceMultiplicityOne : usc_FaceMultiplicityOne unitCell ucBase :=
  usc_unitCell_faceMultiplicityOne





theorem emb_domino_faceMultiplicityOne : usc_FaceMultiplicityOne domino dmBase :=
  usc_domino_faceMultiplicityOne













theorem emb_orbitFaceNoPinch_of_noDiagTouch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npd_NoDiagTouch K) :
    OrbitFaceNoPinch K a :=
  (usc_faceMultiplicityOne_iff_noPinch K a).mp (emb_faceMultiplicityOne_of_noDiagTouch K a h)










theorem emb_orbit_isCycle_of_noDiagTouch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a)
    (h : npd_NoDiagTouch K) :
    ((dartOrbitFaceWalk K a.1 a.2 (dartOrbitPeriod K a)).copy rfl
      (by rw [orbit_iterate_period_eq K a])).IsCycle :=
  usc_orbit_isCycle K a hp (emb_orbitFaceNoPinch_of_noDiagTouch K a h)







theorem emb_orbit_isCycle_of_kingSaturated (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a)
    (h : npm_KingSaturated K) :
    ((dartOrbitFaceWalk K a.1 a.2 (dartOrbitPeriod K a)).copy rfl
      (by rw [orbit_iterate_period_eq K a])).IsCycle :=
  emb_orbit_isCycle_of_noDiagTouch K a hp (npm_noDiagTouch_of_kingSaturated h)











































end Lattice

end StatMech
