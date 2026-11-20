/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.Lattice.InsideConnected
import Code.Lattice.EulerGeometricFaces
import Code.Lattice.StraightWalk
import Code.Walls.wnbenoboundedeven
import Code.Walls.wchcovering
import Code.Walls.wicinterior

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}




theorem wlr_leftBoundary_off (Vc : (hypercubicLattice 2).Walk a a) {w : Site 2}
    (hw : w ∈ wic_leftBoundary Vc) : w ∉ Vc.support := hw.2.1


theorem wlr_leftBoundary_interior (Vc : (hypercubicLattice 2).Walk a a) {w : Site 2}
    (hw : w ∈ wic_leftBoundary Vc) : w ∈ jec_leftRegion Vc := hw.1


theorem wlr_leftBoundary_westSupport (Vc : (hypercubicLattice 2).Walk a a) {w : Site 2}
    (hw : w ∈ wic_leftBoundary Vc) : (![w 0 - 1, w 1] : Site 2) ∈ Vc.support := hw.2.2







theorem wlr_horizAdj_reachable (Vc : (hypercubicLattice 2).Walk a a) {c r : ℤ}
    (h0 : (![c, r] : Site 2) ∉ Vc.support) (h1 : (![c + 1, r] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![c, r] : Site 2) (![c + 1, r] : Site 2) := by
  have hadj : (hypercubicLattice 2).Adj (![c, r] : Site 2) (![c + 1, r] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ((offSupport_adj Vc _ _).mpr ⟨hadj, h0, h1⟩).reachable


theorem wlr_vertAdj_reachable (Vc : (hypercubicLattice 2).Walk a a) {c r : ℤ}
    (h0 : (![c, r] : Site 2) ∉ Vc.support) (h1 : (![c, r + 1] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![c, r] : Site 2) (![c, r + 1] : Site 2) := by
  have hadj : (hypercubicLattice 2).Adj (![c, r] : Site 2) (![c, r + 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ((offSupport_adj Vc _ _).mpr ⟨hadj, h0, h1⟩).reachable



theorem wlr_adjacent_reachable (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v) (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (offSupport Vc).Reachable u v :=
  ((offSupport_adj Vc _ _).mpr ⟨hadj, hu, hv⟩).reachable




theorem wlr_vertWall_reachable (Vc : (hypercubicLattice 2).Walk a a) (c r0 r1 : ℤ)
    (hoff : ∀ t : ℤ, t ∈ Set.uIcc r0 r1 → (![c, t] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![c, r0] : Site 2) (![c, r1] : Site 2) :=
  wnbe_vertRun_reachable Vc c r0 r1 hoff



theorem wlr_horizRun_reachable (Vc : (hypercubicLattice 2).Walk a a) (r x0 x1 : ℤ)
    (hoff : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, r] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![x0, r] : Site 2) (![x1, r] : Site 2) :=
  wnbe_horizRun_reachable Vc r x0 x1 hoff











def wlr_innerRing (Vc : (hypercubicLattice 2).Walk a a) : Set (Site 2) :=
  {w | w ∈ jec_leftRegion Vc ∧ w ∉ Vc.support ∧
    ∃ nb : Site 2, (hypercubicLattice 2).Adj w nb ∧ nb ∈ Vc.support}



theorem wlr_leftBoundary_subset_innerRing (Vc : (hypercubicLattice 2).Walk a a) :
    wic_leftBoundary Vc ⊆ wlr_innerRing Vc := by
  rintro w ⟨hint, hoff, hwest⟩
  refine ⟨hint, hoff, (![w 0 - 1, w 1] : Site 2), ?_, hwest⟩
  have : w = (![w 0, w 1] : Site 2) := (wic_eta w).symm
  rw [this]
  simp [hypercubicLattice_adj, Fin.sum_univ_two]





def wlr_InnerRingConnected (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ u v : Site 2, u ∈ wlr_innerRing Vc → v ∈ wlr_innerRing Vc → (offSupport Vc).Reachable u v




theorem wlr_leftBoundaryConnected_of_innerRingConnected (Vc : (hypercubicLattice 2).Walk a a)
    (h : wlr_InnerRingConnected Vc) : wic_LeftBoundaryConnected Vc := by
  intro u v hu hv
  exact h u v (wlr_leftBoundary_subset_innerRing Vc hu) (wlr_leftBoundary_subset_innerRing Vc hv)






theorem wlr_winding_separation_of_innerRing (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
    {sIn : Site 2} (hsInmem : sIn ∈ jec_leftRegion Vc) (hsInoff : sIn ∉ Vc.support)
    (hres : wlr_InnerRingConnected Vc)
    (hNoBddEven : woc_NoBoundedEvenComponent Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 :=
  wic_winding_separation_of_residue Vc R hsupp hsInmem hsInoff
    (wlr_leftBoundaryConnected_of_innerRingConnected Vc hres) hNoBddEven














theorem wlr_support_connected (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2}
    (hu : u ∈ Vc.support) (hv : v ∈ Vc.support) :
    ∃ p : (hypercubicLattice 2).Walk u v, ∀ z ∈ p.support, z ∈ Vc.support := by
  refine ⟨(Vc.takeUntil u hu).reverse.append (Vc.takeUntil v hv), ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_append] at hz
  rcases List.mem_append.mp hz with h | h
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h
    exact Vc.support_takeUntil_subset_support hu h
  · exact Vc.support_takeUntil_subset_support hv (List.tail_subset _ h)






















def wlr_ConsecutiveInnerStep (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ s s' w w' : Site 2, s ∈ Vc.support → s' ∈ Vc.support →
    (hypercubicLattice 2).Adj s s' →
    w ∈ wlr_innerRing Vc → (hypercubicLattice 2).Adj w s →
    w' ∈ wlr_innerRing Vc → (hypercubicLattice 2).Adj w' s' →
    (offSupport Vc).Reachable w w'

end Lattice

end StatMech
