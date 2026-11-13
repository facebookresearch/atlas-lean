/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Mathlib
import Code.RSW.Defs
import Code.RSW.SelfDuality
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace RSW

namespace CrossingDuality











theorem rcd_crossingPair_incompatible (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    ¬ (ω e = true ∧ dualConfig ω (crossEdge e) = true) :=
  StatMech.RSW.crossingPair_incompatible ω e







theorem rcd_open_blocks_dual (ω : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y)
    {x' y' : Site 2} (w' : (openSubgraph 2 (dualConfig ω)).Walk x' y')
    (e : Sym2 (Site 2)) (he : e ∈ w.edges) (he' : crossEdge e ∈ w'.edges) :
    False :=
  StatMech.RSW.openWalk_blocks_dualWalk ω w w' e he he'
















def rcd_dualBox (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  dualVerticalCrossingEvent (a + 1) (b - 1) c d

@[simp] theorem rcd_mem_dualBox {a b c d : ℤ} {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ rcd_dualBox a b c d ↔ DualVerticalCrossing ω (a + 1) (b - 1) c d := Iff.rfl














def rcd_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Set (Site 2) :=
  {v | v ∈ rect a b c d ∧ ∃ (x : Site 2) (hx : x ∈ leftSide a b c d) (hv : v ∈ rect a b c d),
      ConnectedWithin 2 ω (rect a b c d) ⟨x, leftSide_subset hx⟩ ⟨v, hv⟩}

theorem rcd_leftReach_subset_box (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) :
    rcd_leftReach ω a b c d ⊆ rect a b c d := fun _ hv => hv.1


theorem rcd_leftReach_finite (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) :
    (rcd_leftReach ω a b c d).Finite :=
  (rect_finite a b c d).subset (rcd_leftReach_subset_box ω a b c d)



theorem rcd_horizontal_iff_right_in_leftReach (ω : ConfigSpace (Sym2 (Site 2)))
    (a b c d : ℤ) :
    HorizontalCrossing ω a b c d ↔
      ∃ y : Site 2, y ∈ rightSide a b c d ∧ y ∈ rcd_leftReach ω a b c d := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨y, y.2, rightSide_subset y.2, ⟨x, x.2, rightSide_subset y.2, hxy⟩⟩
  · rintro ⟨y, hyR, _hybox, x, hxL, hyb, hconn⟩
    exact ⟨⟨x, hxL⟩, ⟨y, hyR⟩, hconn⟩


theorem rcd_no_horizontal_iff_right_unreachable (ω : ConfigSpace (Sym2 (Site 2)))
    (a b c d : ℤ) :
    ¬ HorizontalCrossing ω a b c d ↔
      ∀ y : Site 2, y ∈ rightSide a b c d → y ∉ rcd_leftReach ω a b c d := by
  rw [rcd_horizontal_iff_right_in_leftReach]
  push Not
  rfl



theorem rcd_leftReach_extend (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) {v w : Site 2}
    (hv : v ∈ rcd_leftReach ω a b c d) (hwbox : w ∈ rect a b c d)
    (hadj : (hypercubicLattice 2).Adj v w) (hopen : ω s(v, w) = true) :
    w ∈ rcd_leftReach ω a b c d := by
  obtain ⟨hvbox, x, hxL, hvbox', hconn⟩ := hv
  refine ⟨hwbox, x, hxL, hwbox, ?_⟩
  have hstep : (openSubgraphInduce 2 ω (rect a b c d)).Adj ⟨v, hvbox'⟩ ⟨w, hwbox⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hadj, hopen⟩
  exact hconn.trans hstep.reachable




theorem rcd_leftReach_boundary_closed (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ)
    {v w : Site 2} (hv : v ∈ rcd_leftReach ω a b c d) (hwbox : w ∈ rect a b c d)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ rcd_leftReach ω a b c d) :
    ω s(v, w) = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  exact hw (rcd_leftReach_extend ω a b c d hv hwbox hadj h)





theorem rcd_leftReach_boundary_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ)
    {v w : Site 2} (hv : v ∈ rcd_leftReach ω a b c d) (hwbox : w ∈ rect a b c d)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ rcd_leftReach ω a b c d) :
    dualConfig ω (crossEdge s(v, w)) = true := by
  rw [StatMech.RSW.dualCross_open_iff_closed]
  exact rcd_leftReach_boundary_closed ω a b c d hv hwbox hadj hw


theorem rcd_leftReach_disjoint_rightSide (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ)
    (hnoH : ¬ HorizontalCrossing ω a b c d) :
    Disjoint (rcd_leftReach ω a b c d) (rightSide a b c d) := by
  rw [Set.disjoint_right]
  intro y hyR hyL
  exact (rcd_no_horizontal_iff_right_unreachable ω a b c d).mp hnoH y hyR hyL















theorem rcd_separation (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ)
    (hnoH : ¬ HorizontalCrossing ω a b c d) :
    (rcd_leftReach ω a b c d).Finite ∧
      (∀ x ∈ leftSide a b c d, x ∈ rcd_leftReach ω a b c d) ∧
      Disjoint (rcd_leftReach ω a b c d) (rightSide a b c d) ∧
      (∀ {v w : Site 2}, v ∈ rcd_leftReach ω a b c d → w ∈ rect a b c d →
        (hypercubicLattice 2).Adj v w → w ∉ rcd_leftReach ω a b c d →
        ω s(v, w) = false ∧ dualConfig ω (crossEdge s(v, w)) = true) := by
  refine ⟨rcd_leftReach_finite ω a b c d, ?_,
    rcd_leftReach_disjoint_rightSide ω a b c d hnoH, ?_⟩
  · intro x hx
    exact ⟨leftSide_subset hx, x, hx, leftSide_subset hx,
      connectedWithin_refl ω (rect a b c d) ⟨x, leftSide_subset hx⟩⟩
  · intro v w hv hwbox hadj hw
    exact ⟨rcd_leftReach_boundary_closed ω a b c d hv hwbox hadj hw,
      rcd_leftReach_boundary_dual_open ω a b c d hv hwbox hadj hw⟩

end CrossingDuality

end RSW

end StatMech
