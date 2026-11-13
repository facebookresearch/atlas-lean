/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.RSW.Defs
import Code.Lattice.CrossingParity
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.FaceRegion
import Code.RSW.SelfDuality

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}






def bcd_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Set (Site 2) :=
  {v | v ∈ rect 0 n 0 n ∧ ∃ (x : Site 2) (hx : x ∈ leftSide 0 n 0 n) (hv : v ∈ rect 0 n 0 n),
      ConnectedWithin 2 ω (rect 0 n 0 n) ⟨x, leftSide_subset hx⟩ ⟨v, hv⟩}

theorem bcd_leftReach_subset_box (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    bcd_leftReach ω n ⊆ rect 0 n 0 n := fun _ hv => hv.1



theorem bcd_horizontal_iff_right_in_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    HorizontalCrossing ω 0 n 0 n ↔
      ∃ y : Site 2, y ∈ rightSide 0 n 0 n ∧ y ∈ bcd_leftReach ω n := by
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨y, y.2, rightSide_subset y.2, ?_⟩
    exact ⟨x, x.2, rightSide_subset y.2, hxy⟩
  · rintro ⟨y, hyR, _hybox, x, hxL, hyb, hconn⟩
    exact ⟨⟨x, hxL⟩, ⟨y, hyR⟩, hconn⟩



theorem bcd_no_horizontal_iff_right_unreachable (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    ¬ HorizontalCrossing ω 0 n 0 n ↔
      ∀ y : Site 2, y ∈ rightSide 0 n 0 n → y ∉ bcd_leftReach ω n := by
  rw [bcd_horizontal_iff_right_in_leftReach]
  push Not
  rfl















theorem bcd_leftReach_extend (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (hv : v ∈ bcd_leftReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hopen : ω s(v, w) = true) :
    w ∈ bcd_leftReach ω n := by
  obtain ⟨hvbox, x, hxL, hvbox', hconn⟩ := hv
  refine ⟨hwbox, x, hxL, hwbox, ?_⟩
  
  have hstep : (openSubgraphInduce 2 ω (rect 0 n 0 n)).Adj ⟨v, hvbox'⟩ ⟨w, hwbox⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hadj, hopen⟩
  exact hconn.trans hstep.reachable




theorem bcd_leftReach_boundary_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcd_leftReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcd_leftReach ω n) :
    ω s(v, w) = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  exact hw (bcd_leftReach_extend ω n hv hwbox hadj h)








theorem bcd_leftReach_boundary_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcd_leftReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcd_leftReach ω n) :
    dualConfig ω (crossEdge s(v, w)) = true := by
  rw [StatMech.RSW.dualCross_open_iff_closed]
  exact bcd_leftReach_boundary_closed ω n hv hwbox hadj hw


theorem bcd_leftReach_finite (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (bcd_leftReach ω n).Finite :=
  (rect_finite 0 n 0 n).subset (bcd_leftReach_subset_box ω n)






theorem bcd_leftReach_disjoint_rightSide (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    Disjoint (bcd_leftReach ω n) (rightSide 0 n 0 n) := by
  rw [Set.disjoint_right]
  intro y hyR hyL
  exact (bcd_no_horizontal_iff_right_unreachable ω n).mp hnoH y hyR hyL
















theorem bcd_crossing_edges_incompatible (ω : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y)
    {x' y' : Site 2} (w' : (openSubgraph 2 (dualConfig ω)).Walk x' y')
    (e : Sym2 (Site 2)) (he : e ∈ w.edges) (he' : crossEdge e ∈ w'.edges) :
    False :=
  StatMech.RSW.openWalk_blocks_dualWalk ω w w' e he he'






























theorem bcd_separation (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    (bcd_leftReach ω n).Finite ∧
      (∀ x ∈ leftSide 0 n 0 n, x ∈ bcd_leftReach ω n) ∧
      Disjoint (bcd_leftReach ω n) (rightSide 0 n 0 n) ∧
      (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n →
        (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n →
        ω s(v, w) = false ∧ dualConfig ω (crossEdge s(v, w)) = true) := by
  refine ⟨bcd_leftReach_finite ω n, ?_, bcd_leftReach_disjoint_rightSide ω n hnoH, ?_⟩
  · 
    intro x hx
    refine ⟨leftSide_subset hx, x, hx, leftSide_subset hx, ?_⟩
    exact connectedWithin_refl ω (rect 0 n 0 n) ⟨x, leftSide_subset hx⟩
  · intro v w hv hwbox hadj hw
    exact ⟨bcd_leftReach_boundary_closed ω n hv hwbox hadj hw,
      bcd_leftReach_boundary_dual_open ω n hv hwbox hadj hw⟩

end Universality

end StatMech
