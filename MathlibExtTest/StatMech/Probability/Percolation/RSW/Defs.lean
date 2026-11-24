/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.Defs

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.Defs`

Tests rectangle geometry, open and dual horizontal crossing events, annulus membership,
`boxCrossingEvent`, and the named box-crossing properties `P5` and `P5c`.
-/

@[expose] public section

open MeasureTheory StatMech StatMech.RSW StatMech.RSW.Box StatMech.Lattice

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.Defs

-- `rect` membership.
example : (![1, 0] : Site 2) ∈ rect 0 1 0 0 := by simp [mem_rect]

example : (![0, 2] : Site 2) ∉ rect 0 1 0 1 := by simp [mem_rect]

-- The all-open configuration crosses `[0, 1] × [0, 0]`.
theorem allOpen_mem_horizontalCrossingEvent :
    (fun _ => true : ConfigSpace (Sym2 (Site 2))) ∈ horizontalCrossingEvent 0 1 0 0 := by
  refine ⟨⟨![0, 0], by simp [mem_rect]⟩, ⟨![1, 0], by simp [mem_rect]⟩, ?_⟩
  refine SimpleGraph.Adj.reachable ?_
  rw [openSubgraphInduce_adj, openSubgraph_adj]
  refine ⟨?_, rfl⟩
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

-- Monotonicity of the crossing event.
example (ω : ConfigSpace (Sym2 (Site 2))) (h : ω ∈ horizontalCrossingEvent 0 1 0 0) :
    (fun _ => true : ConfigSpace (Sym2 (Site 2))) ∈ horizontalCrossingEvent 0 1 0 0 :=
  Box.horizontalCrossingEvent_increasing (fun _ => Bool.le_true _) h

-- The two vertices of `[0, 1] × [0, 0]` force any crossing to use their common edge.
private theorem unitRow_crossing_iff_adj (G : SimpleGraph (Site 2)) :
    (∃ (x : leftSide 0 1 0 0) (y : rightSide 0 1 0 0),
      (G.induce (rect 0 1 0 0)).Reachable
        ⟨x.val, leftSide_subset x.2⟩ ⟨y.val, rightSide_subset y.2⟩) ↔
      G.Adj ![0, 0] ![1, 0] := by
  have site_eq (z : Site 2) (a b : ℤ) (h0 : z 0 = a) (h1 : z 1 = b) :
      z = ![a, b] := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have second_eq (z : Site 2) (hz : z ∈ rect 0 1 0 0) : z 1 = 0 :=
    le_antisymm hz.2.2.2 hz.2.2.1
  constructor
  · rintro ⟨x, y, ⟨p⟩⟩
    have hne : (⟨x.val, leftSide_subset x.2⟩ : rect 0 1 0 0) ≠
        ⟨y.val, rightSide_subset y.2⟩ := by
      intro heq
      have hxy := congrArg (fun z : rect 0 1 0 0 => z.val 0) heq
      exact (by decide : (0 : ℤ) ≠ 1) (x.2.2.symm.trans (hxy.trans y.2.2))
    obtain ⟨z, hxz, _, _⟩ := p.exists_eq_cons_of_ne hne
    change G.Adj x.val z.val at hxz
    rw [site_eq x.val 0 0 x.2.2 (second_eq _ x.2.1)] at hxz
    have hz := mem_rect.mp z.2
    have hz0 : z.val 0 = 0 ∨ z.val 0 = 1 := by omega
    rcases hz0 with hz0 | hz0
    · rw [site_eq z.val 0 0 hz0 (second_eq _ z.2)] at hxz
      exact (G.irrefl hxz).elim
    · rwa [site_eq z.val 1 0 hz0 (second_eq _ z.2)] at hxz
  · intro h
    exact ⟨⟨![0, 0], by simp⟩, ⟨![1, 0], by simp⟩, SimpleGraph.Adj.reachable h⟩

private theorem unitRow_dual_event_iff (ω : ConfigSpace (Sym2 (Site 2))) :
    ω ∈ dualHorizontalCrossingEvent 0 1 0 0 ↔ ω s(![1, 0], ![1, 1]) = false := by
  have hedge : sharedPrimalEdge ![0, 0] ![1, 0] = s(![1, 0], ![1, 1]) :=
    sharedPrimalEdge_right 0 0
  have hright : (hypercubicLattice 2).Adj ![0, 0] ![1, 0] := latAdj_right 0 0
  have htop : (hypercubicLattice 2).Adj ![1, 0] ![1, 1] := latAdj_top 1 0
  rw [mem_dualHorizontalCrossingEvent, DualHorizontalCrossing, unitRow_crossing_iff_adj,
    whb_faceRegion_adj, hedge, SimpleGraph.mem_edgeSet, openSubgraph_adj,
    and_iff_right hright, and_iff_right htop]
  cases ω s(![1, 0], ![1, 1]) <;> simp

private theorem unitRow_rotated_iff (ω : ConfigSpace (Sym2 (Site 2))) :
    HorizontalCrossing (dualConfig ω) 0 1 0 0 ↔ ω s(![0, 0], ![0, -1]) = false := by
  have hright : (hypercubicLattice 2).Adj ![0, 0] ![1, 0] := latAdj_right 0 0
  refine (unitRow_crossing_iff_adj (openSubgraph 2 (dualConfig ω))).trans ?_
  rw [openSubgraph_adj, and_iff_right hright, dual_isOpen_iff_isClosed]
  rfl

-- Issue #5119: the two encodings read different primal bonds, even in a two-vertex box.
example : ∃ ω, ω ∈ dualHorizontalCrossingEvent 0 1 0 0 ∧
    ¬ HorizontalCrossing (dualConfig ω) 0 1 0 0 := by
  classical
  let ω : ConfigSpace (Sym2 (Site 2)) :=
    fun e => if e = s(![1, 0], ![1, 1]) then false else true
  refine ⟨ω, ?_⟩
  have hne : (s(![0, 0], ![0, -1]) : Sym2 (Site 2)) ≠ s(![1, 0], ![1, 1]) := by
    simp [funext_iff, Fin.forall_fin_two]
  rw [unitRow_dual_event_iff, unitRow_rotated_iff]
  simp [ω, hne]

example (ω : ConfigSpace (Sym2 (Site 2))) (h : ω ∈ dualHorizontalCrossingEvent 0 1 0 0) :
    (fun _ => false : ConfigSpace (Sym2 (Site 2))) ∈ dualHorizontalCrossingEvent 0 1 0 0 :=
  dualHorizontalCrossingEvent_antitone (fun _ => Bool.false_le _) h

example (ω ω' : ConfigSpace (Sym2 (Site 2))) (h : dualConfig ω ≤ dualConfig ω')
    (hω : ω ∈ dualHorizontalCrossingEvent 0 1 0 0) :
    ω' ∈ dualHorizontalCrossingEvent 0 1 0 0 :=
  dualHorizontalCrossingEvent_increasing h hω

-- Coincident sides permit a length-zero crossing even when all primal edges are open.
example : (fun _ => true : ConfigSpace (Sym2 (Site 2))) ∈ dualHorizontalCrossingEvent 2 2 1 3 := by
  rw [mem_dualHorizontalCrossingEvent, dualHorizontalCrossing_iff]
  exact ⟨⟨![2, 1], by simp⟩, ⟨![2, 1], by simp⟩, Relation.ReflTransGen.refl⟩

-- Reversing either interval makes the dual rectangle empty.
example (ω : ConfigSpace (Sym2 (Site 2))) : ω ∉ dualHorizontalCrossingEvent 1 0 0 0 := by
  rw [mem_dualHorizontalCrossingEvent, dualHorizontalCrossing_iff]
  rintro ⟨x, _, _⟩
  have hx := mem_rect.mp x.2.1
  omega

example (ω : ConfigSpace (Sym2 (Site 2))) : ω ∉ dualHorizontalCrossingEvent 0 0 1 0 := by
  rw [mem_dualHorizontalCrossingEvent, dualHorizontalCrossing_iff]
  rintro ⟨x, _, _⟩
  have hx := mem_rect.mp x.2.1
  omega

-- Rectangle crossing events are genuine measurable events on the infinite bond cube.
example : MeasurableSet (horizontalCrossingEvent 0 1 0 0) :=
  measurableSet_horizontalCrossingEvent 0 1 0 0

example : MeasurableSet (verticalCrossingEvent 0 1 0 0) :=
  measurableSet_verticalCrossingEvent 0 1 0 0

-- `(2, 0)` lies in the annulus `Λ_2 \ Λ_1` around the origin.
example : (![2, 0] : Site 2) ∈ annulus 0 1 := by
  rw [mem_annulus]
  refine ⟨![2, 0], ⟨?_, ?_⟩, by simp⟩
  · rw [mem_box]; intro i; fin_cases i <;> simp
  · rw [mem_box]; push Not; exact ⟨0, by simp⟩

-- `boxCrossingEvent` unfolds to a rectangle crossing.
example : boxCrossingEvent 2 3 = horizontalCrossingEvent 0 6 0 3 := by
  simp only [boxCrossingEvent]
  norm_num

-- `P5` and `P5c` for constant set functions.
example : P5 (fun _ _ => 1) := fun _ _ => ⟨1, one_pos, fun _ => le_rfl⟩

theorem p5c_half : P5c (Ξ := Unit) (fun _ _ _ => 1 / 2) :=
  fun _ _ => ⟨1 / 2, by norm_num, fun _ _ => ⟨le_rfl, by norm_num⟩⟩

example : P5 (fun _ _ => (1 / 2 : ℝ)) := p5c_half.p5 ()

end MathlibExtTest.StatMech.Probability.Percolation.RSW.Defs
