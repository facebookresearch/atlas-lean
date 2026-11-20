/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnCutTopology
import Code.FrontierD.FKRectCutSquareEmbedding








open Equiv Finset SimpleGraph

namespace StatMech.FrontierD

open StatMech.Onsager StatMech.Onsager.BaseCase

noncomputable section

private theorem fkRectPathDisplacement_row_eq_sum
    (l : List (Fin 4)) :
    (ons_pathDisplacement l).1 - (ons_pathDisplacement l).2 =
      (l.map fun k => (stepOf k).1 - (stepOf k).2).sum := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [ons_pathDisplacement, List.map_cons, List.sum_cons,
      Prod.fst_add, Prod.snd_add]
    linear_combination ih

private theorem fkRectRefinedBoundaryCanonicalCenter_row
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    (fkRectRefinedBoundaryCanonicalCenter R d).1 -
        (fkRectRefinedBoundaryCanonicalCenter R d).2 =
      4 * (d.1.2.val : Int) - 2 := by
  let e := fkRectTorusMedialEdgeEquiv R d.1
  have hdrow : d.1.2 = e.2.2 := by
    rw [← fkRectTorusMedialEdgeEquiv_symm_snd R e]
    simp [e]
  unfold fkRectRefinedBoundaryCanonicalCenter
  rw [show fkRectTorusMedialEdgeEquiv R d.1 = e from rfl, hdrow]
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkRectRefinedPrimalEdgeCenter, fkRectLiftedIndexedEdgeEnds,
      fkRectSquareDevelopPoint, hy] <;> omega

private theorem fkRectBlackDartShiftedPoint_zero_row
    (R : FKRectTorus) (d : FKMedialBlackDart R.medialTorus) :
    (fkRectBlackDartShiftedPoint R (0, 0) d).1 -
        (fkRectBlackDartShiftedPoint R (0, 0) d).2 =
      4 * (d.1.1.2.val : Int) - 2 +
        ((fkRectRefinedSideOffset d.1.2).1 -
          (fkRectRefinedSideOffset d.1.2).2) := by
  unfold fkRectBlackDartShiftedPoint fkRectRefinedDartPoint
  simp only [fkRectSquareDeckTranslation, mul_zero, add_zero,
    Prod.fst, Prod.snd]
  have hcenter := fkRectRefinedBoundaryCanonicalCenter_row R d.1
  omega




private theorem fkRectBlackBoundaryStep_row_eq_potential_sub_of_avoidsSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C)
    (d : FKMedialBlackDart R.medialTorus)
    (hdC : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        d.1 = C) :
    2 * ((stepOf (fkMedialStrandDirection
      (fkRectConfigurationToMedialPairing R omega) d.1)).1 -
        (stepOf (fkMedialStrandDirection
          (fkRectConfigurationToMedialPairing R omega) d.1)).2) =
      ((fkRectBlackDartShiftedPoint R (0, 0)
          (fkMedialBlackBoundaryPerm
            (fkRectConfigurationToMedialPairing R omega) d)).1 -
        (fkRectBlackDartShiftedPoint R (0, 0)
          (fkMedialBlackBoundaryPerm
            (fkRectConfigurationToMedialPairing R omega) d)).2) -
      ((fkRectBlackDartShiftedPoint R (0, 0) d).1 -
        (fkRectBlackDartShiftedPoint R (0, 0) d).2) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  change (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
      d.1 = C at hdC
  change 2 * ((stepOf (fkMedialStrandDirection pairing d.1)).1 -
      (stepOf (fkMedialStrandDirection pairing d.1)).2) = _
  rw [fkRectBlackDartShiftedPoint_zero_row,
    fkRectBlackDartShiftedPoint_zero_row]
  rcases d with ⟨⟨⟨i, j⟩, side⟩, hd⟩
  cases hp : pairing (i, j) <;> cases side
  all_goals simp only [fkMedialBlackBoundaryPerm_val,
    fkMedialLocalMate, fkMedialBondMate, pairing, hp,
    fkMedialStrandDirection, fkRectRefinedSideOffset, stepOf,
    Prod.fst, Prod.snd]
  all_goals try rw [finitePeriodicSucc_val R.medialTorus.height_pos]
  all_goals try rw [fkRectCyclicPred_val R.medialTorus.height_pos]
  all_goals try split
  all_goals try omega
  all_goals exfalso
  all_goals
    apply havoid
    refine ⟨i, ?_⟩
    rw [← hdC]
    change (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
        (fkMedialVerticalSeamDart R.medialTorus i) = _
  case false.west.isTrue =>
    have hj : j = svFinLast R.medialTorus.height_pos := by
      ext
      simp [svFinLast]
      omega
    subst j
    rw [show fkMedialVerticalSeamDart R.medialTorus i =
        fkMedialLocalMate pairing
          ((i, svFinLast R.medialTorus.height_pos), .west) by
      simp [fkMedialVerticalSeamDart, fkMedialLocalMate, hp]]
    simpa using connectedComponentMk_localMate pairing
      ((i, svFinLast R.medialTorus.height_pos), .west)
  case true.east.isTrue =>
    have hj : j = svFinLast R.medialTorus.height_pos := by
      ext
      simp [svFinLast]
      omega
    subst j
    rw [show fkMedialVerticalSeamDart R.medialTorus i =
        fkMedialLocalMate pairing
          ((i, svFinLast R.medialTorus.height_pos), .east) by
      simp [fkMedialVerticalSeamDart, fkMedialLocalMate, hp]]
    simpa using connectedComponentMk_localMate pairing
      ((i, svFinLast R.medialTorus.height_pos), .east)
  case false.east.isTrue =>
    have hj : j = (⟨0, R.medialTorus.height_pos⟩ :
        Fin R.medialTorus.height) := by ext; omega
    subst j
    apply SimpleGraph.ConnectedComponent.sound
    convert (fkMedialBoundaryStep_reachable pairing
      ((i, (⟨0, R.medialTorus.height_pos⟩ :
        Fin R.medialTorus.height)), .east)).symm using 1
    simp [fkMedialVerticalSeamDart, fkMedialBoundaryStep_apply,
      fkMedialLocalMate, fkMedialBondMate, hp, svCyclicPred_zero]
  case true.west.isTrue =>
    have hj : j = (⟨0, R.medialTorus.height_pos⟩ :
        Fin R.medialTorus.height) := by ext; omega
    subst j
    apply SimpleGraph.ConnectedComponent.sound
    convert (fkMedialBoundaryStep_reachable pairing
      ((i, (⟨0, R.medialTorus.height_pos⟩ :
        Fin R.medialTorus.height)), .west)).symm using 1
    simp [fkMedialVerticalSeamDart, fkMedialBoundaryStep_apply,
      fkMedialLocalMate, fkMedialBondMate, hp, svCyclicPred_zero]

private theorem fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∈ fkRectHorizontalCutEdges R) :
    fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val = 0 at ha
  have hlast : R.height - 1 + 1 = R.height := by omega
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk]
    all_goals rw [fkRectCyclicPred_val]
    all_goals simp only [ha, if_true]
    all_goals exact Or.inl ⟨True.intro, hlast⟩
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk]
    rw [fkRectCyclicPred_val]
    simp only [ha, if_true]
    exact Or.inl ⟨True.intro, hlast⟩

private theorem fkRectCrossesHorizontalSeam_indexedEdge_of_verticalCut
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∈ fkRectVerticalCutEdges R) :
    fkRectCrossesHorizontalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectVerticalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  rcases ha with ⟨rfl, hx⟩
  change x.val = 0 at hx
  have hlast : R.width - 1 + 1 = R.width := by omega
  by_cases hy : Even y.val <;>
    simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
      hy, if_true, fkRectCrossesHorizontalSeam_mk]
  all_goals rw [fkRectCyclicPred_val]
  all_goals simp only [hx, if_true]
  all_goals
    first
    | exact Or.inl ⟨True.intro, hlast⟩
    | exact Or.inr ⟨True.intro, hlast⟩

private theorem fkRectForceCutClosed_adj_of_not_crossesSeams
    (R : FKRectTorus) (omega : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R omega).Adj x y)
    (hh : ¬ fkRectCrossesHorizontalSeam R s(x, y))
    (hv : ¬ fkRectCrossesVerticalSeam R s(x, y)) :
    (fkRectOpenGraph R (fkRectForceCutClosed R omega)).Adj x y := by
  rcases hxy with ⟨a, hopen, hedge⟩
  refine ⟨a, ?_, hedge⟩
  have hnot : a ∉ fkRectTorusCutEdges R := by
    intro hcut
    rw [fkRectTorusCutEdges, Finset.mem_union] at hcut
    rcases hcut with hcut | hcut
    · apply hv
      rw [← hedge]
      exact fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut R a hcut
    · apply hh
      rw [← hedge]
      exact fkRectCrossesHorizontalSeam_indexedEdge_of_verticalCut R a hcut
  rw [fkRectForceCutClosed_of_not_mem R omega a hnot, hopen]

private noncomputable def fkRectRightComponentPotential
    (R : FKRectTorus) (eta : R.Configuration) (x : R.Vertex) : Int := by
  classical
  exact if ∃ z : Fin R.height,
    (fkRectOpenGraph R eta).connectedComponentMk x =
      (fkRectOpenGraph R eta).connectedComponentMk
        (fkRectRightColumn R, z) then 1 else 0

@[simp] private theorem fkRectRightComponentPotential_right
    (R : FKRectTorus) (eta : R.Configuration) (z : Fin R.height) :
    fkRectRightComponentPotential R eta (fkRectRightColumn R, z) = 1 := by
  classical
  unfold fkRectRightComponentPotential
  rw [if_pos ⟨z, rfl⟩]

private theorem fkRectRightComponentPotential_left_eq_zero_of_noCrossing
    (R : FKRectTorus) (eta : R.Configuration)
    (hno : ∀ C : (fkRectOpenGraph R eta).ConnectedComponent,
      ¬ FKRectRawHorizontalCrossingComponent R eta C)
    (z : Fin R.height) :
    fkRectRightComponentPotential R eta (fkRectLeftColumn R, z) = 0 := by
  unfold fkRectRightComponentPotential
  split
  · rename_i hright
    obtain ⟨w, hw⟩ := hright
    exfalso
    apply hno ((fkRectOpenGraph R eta).connectedComponentMk
      (fkRectLeftColumn R, z))
    exact ⟨⟨z, rfl⟩, ⟨w, hw.symm⟩⟩
  · rfl

private theorem fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses
    (R : FKRectTorus) (x y : R.Vertex)
    (h : ¬ fkRectCrossesHorizontalSeam R s(x, y)) :
    fkRectHorizontalSeamIncrement R x y = 0 := by
  unfold fkRectHorizontalSeamIncrement
  by_cases hxy : x.1.val + 1 = R.width ∧ y.1.val = 0
  · exfalso
    apply h
    exact (fkRectCrossesHorizontalSeam_mk R x y).2 (Or.inr ⟨hxy.2, hxy.1⟩)
  · by_cases hyx : x.1.val = 0 ∧ y.1.val + 1 = R.width
    · exfalso
      apply h
      exact (fkRectCrossesHorizontalSeam_mk R x y).2 (Or.inl hyx)
    · simp [hxy, hyx]

private theorem fkRectHorizontalIncrement_eq_potential_sub_of_noCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (hno : ∀ C : (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).ConnectedComponent,
      ¬ FKRectRawHorizontalCrossingComponent R
        (fkRectForceCutClosed R omega) C)
    {x y : R.Vertex} (hxy : (fkRectOpenGraph R omega).Adj x y)
    (hv : ¬ fkRectCrossesVerticalSeam R s(x, y)) :
    fkRectHorizontalSeamIncrement R x y =
      fkRectRightComponentPotential R (fkRectForceCutClosed R omega) x -
        fkRectRightComponentPotential R (fkRectForceCutClosed R omega) y := by
  by_cases hh : fkRectCrossesHorizontalSeam R s(x, y)
  · rw [fkRectCrossesHorizontalSeam_mk] at hh
    rcases hh with ⟨hx0, hyl⟩ | ⟨hy0, hxl⟩
    · have hxleft : x.1 = fkRectLeftColumn R := by
        apply Fin.ext
        simpa [fkRectLeftColumn] using hx0
      have hyright : y.1 = fkRectRightColumn R := by
        apply Fin.ext
        dsimp [fkRectRightColumn]
        omega
      rw [show x = (fkRectLeftColumn R, x.2) by
          exact Prod.ext hxleft rfl,
        show y = (fkRectRightColumn R, y.2) by
          exact Prod.ext hyright rfl,
        fkRectRightComponentPotential_left_eq_zero_of_noCrossing R _ hno,
        fkRectRightComponentPotential_right]
      unfold fkRectHorizontalSeamIncrement
      have hwidth := R.width_gt_two
      simp [fkRectLeftColumn, fkRectRightColumn]
      omega
    · have hyleft : y.1 = fkRectLeftColumn R := by
        apply Fin.ext
        simpa [fkRectLeftColumn] using hy0
      have hxright : x.1 = fkRectRightColumn R := by
        apply Fin.ext
        dsimp [fkRectRightColumn]
        omega
      rw [show x = (fkRectRightColumn R, x.2) by
          exact Prod.ext hxright rfl,
        show y = (fkRectLeftColumn R, y.2) by
          exact Prod.ext hyleft rfl,
        fkRectRightComponentPotential_right,
        fkRectRightComponentPotential_left_eq_zero_of_noCrossing R _ hno]
      unfold fkRectHorizontalSeamIncrement
      have hwidth := R.width_gt_two
      simp [fkRectLeftColumn, fkRectRightColumn]
      omega
  · have hcutAdj := fkRectForceCutClosed_adj_of_not_crossesSeams
      R omega hxy hh hv
    have hcomponent :
        (fkRectOpenGraph R (fkRectForceCutClosed R omega)).connectedComponentMk x =
          (fkRectOpenGraph R (fkRectForceCutClosed R omega)).connectedComponentMk y :=
      SimpleGraph.ConnectedComponent.sound hcutAdj.reachable
    rw [fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses R x y hh]
    unfold fkRectRightComponentPotential
    rw [hcomponent]
    ring

private theorem fkRectWalkWinding_fst_eq_potential_sub_of_noCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (hno : ∀ C : (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).ConnectedComponent,
      ¬ FKRectRawHorizontalCrossingComponent R
        (fkRectForceCutClosed R omega) C)
    {x y : R.Vertex} (p : (fkRectOpenGraph R omega).Walk x y)
    (havoid : ∀ e ∈ p.edges,
      ¬ fkRectCrossesVerticalSeam R e) :
    (fkRectWalkWinding R p).1 =
      fkRectRightComponentPotential R (fkRectForceCutClosed R omega) x -
        fkRectRightComponentPotential R (fkRectForceCutClosed R omega) y := by
  induction p with
  | nil => simp [fkRectWalkWinding]
  | @cons x z y hxz p ih =>
      have hhead : ¬ fkRectCrossesVerticalSeam R s(x, z) :=
        havoid _ (by simp)
      have htail : ∀ e ∈ p.edges,
          ¬ fkRectCrossesVerticalSeam R e := by
        intro e he
        exact havoid e (by simp [he])
      simp only [fkRectWalkWinding, Prod.fst]
      rw [fkRectHorizontalIncrement_eq_potential_sub_of_noCrossing
        R omega hno hxz hhead, ih htail]
      ring



theorem exists_fkRectRawHorizontalCrossingComponent_of_closedWalk
    (R : FKRectTorus) (omega : R.Configuration) {x : R.Vertex}
    (p : (fkRectOpenGraph R omega).Walk x x)
    (havoid : ∀ e ∈ p.edges,
      ¬ fkRectCrossesVerticalSeam R e)
    (hwind : (fkRectWalkWinding R p).1 ≠ 0) :
    ∃ C : (fkRectOpenGraph R
        (fkRectForceCutClosed R omega)).ConnectedComponent,
      FKRectRawHorizontalCrossingComponent R
        (fkRectForceCutClosed R omega) C := by
  by_contra hnone
  push_neg at hnone
  have hzero := fkRectWalkWinding_fst_eq_potential_sub_of_noCrossing
    R omega hnone p havoid
  simp only [sub_self] at hzero
  exact hwind hzero

private theorem fkRectHorizontalIncrement_eq_potential_sub_of_endpointsNoCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex} (hxy : (fkRectOpenGraph R omega).Adj x y)
    (hv : ¬ fkRectCrossesVerticalSeam R s(x, y))
    (hnox : ¬ FKRectRawHorizontalCrossingComponent R
      (fkRectForceCutClosed R omega)
        ((fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk x))
    (hnoy : ¬ FKRectRawHorizontalCrossingComponent R
      (fkRectForceCutClosed R omega)
        ((fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk y)) :
    fkRectHorizontalSeamIncrement R x y =
      fkRectRightComponentPotential R (fkRectForceCutClosed R omega) x -
        fkRectRightComponentPotential R (fkRectForceCutClosed R omega) y := by
  by_cases hh : fkRectCrossesHorizontalSeam R s(x, y)
  · rw [fkRectCrossesHorizontalSeam_mk] at hh
    rcases hh with ⟨hx0, hyl⟩ | ⟨hy0, hxl⟩
    · have hxleft : x.1 = fkRectLeftColumn R := by
        apply Fin.ext
        simpa [fkRectLeftColumn] using hx0
      have hyright : y.1 = fkRectRightColumn R := by
        apply Fin.ext
        dsimp [fkRectRightColumn]
        omega
      have hxzero : fkRectRightComponentPotential R
          (fkRectForceCutClosed R omega) x = 0 := by
        unfold fkRectRightComponentPotential
        split
        · rename_i hright
          obtain ⟨w, hw⟩ := hright
          exfalso
          apply hnox
          exact ⟨⟨x.2, by
            congr 1
            exact Prod.ext hxleft.symm rfl⟩, ⟨w, hw.symm⟩⟩
        · rfl
      rw [hxzero]
      rw [show y = (fkRectRightColumn R, y.2) by
          exact Prod.ext hyright rfl,
        fkRectRightComponentPotential_right]
      unfold fkRectHorizontalSeamIncrement
      have hwidth := R.width_gt_two
      simp [fkRectLeftColumn, fkRectRightColumn]
      omega
    · have hyleft : y.1 = fkRectLeftColumn R := by
        apply Fin.ext
        simpa [fkRectLeftColumn] using hy0
      have hxright : x.1 = fkRectRightColumn R := by
        apply Fin.ext
        dsimp [fkRectRightColumn]
        omega
      have hyzero : fkRectRightComponentPotential R
          (fkRectForceCutClosed R omega) y = 0 := by
        unfold fkRectRightComponentPotential
        split
        · rename_i hright
          obtain ⟨w, hw⟩ := hright
          exfalso
          apply hnoy
          exact ⟨⟨y.2, by
            congr 1
            exact Prod.ext hyleft.symm rfl⟩, ⟨w, hw.symm⟩⟩
        · rfl
      rw [show x = (fkRectRightColumn R, x.2) by
          exact Prod.ext hxright rfl,
        fkRectRightComponentPotential_right, hyzero]
      unfold fkRectHorizontalSeamIncrement
      have hwidth := R.width_gt_two
      simp [fkRectLeftColumn, fkRectRightColumn]
      omega
  · have hcutAdj := fkRectForceCutClosed_adj_of_not_crossesSeams
      R omega hxy hh hv
    have hcomponent :
        (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk x =
        (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk y :=
      SimpleGraph.ConnectedComponent.sound hcutAdj.reachable
    rw [fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses R x y hh]
    unfold fkRectRightComponentPotential
    rw [hcomponent]
    ring

private theorem fkRectWalkWinding_fst_eq_potential_sub_of_supportNoCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex} (p : (fkRectOpenGraph R omega).Walk x y)
    (havoid : ∀ e ∈ p.edges,
      ¬ fkRectCrossesVerticalSeam R e)
    (hno : ∀ z ∈ p.support,
      ¬ FKRectRawHorizontalCrossingComponent R
        (fkRectForceCutClosed R omega)
          ((fkRectOpenGraph R
            (fkRectForceCutClosed R omega)).connectedComponentMk z)) :
    (fkRectWalkWinding R p).1 =
      fkRectRightComponentPotential R (fkRectForceCutClosed R omega) x -
        fkRectRightComponentPotential R (fkRectForceCutClosed R omega) y := by
  induction p with
  | nil => simp [fkRectWalkWinding]
  | @cons x z y hxz p ih =>
      have hhead : ¬ fkRectCrossesVerticalSeam R s(x, z) :=
        havoid _ (by simp)
      have htail : ∀ e ∈ p.edges,
          ¬ fkRectCrossesVerticalSeam R e := by
        intro e he
        exact havoid e (by simp [he])
      have hnox := hno x (by simp [SimpleGraph.Walk.support_cons])
      have hnoTail : ∀ w ∈ p.support,
          ¬ FKRectRawHorizontalCrossingComponent R
            (fkRectForceCutClosed R omega)
              ((fkRectOpenGraph R
                (fkRectForceCutClosed R omega)).connectedComponentMk w) := by
        intro w hw
        exact hno w (by simp [SimpleGraph.Walk.support_cons, hw])
      have hnoz := hnoTail z p.start_mem_support
      simp only [fkRectWalkWinding, Prod.fst]
      rw [fkRectHorizontalIncrement_eq_potential_sub_of_endpointsNoCrossing
        R omega hxz hhead hnox hnoz, ih htail hnoTail]
      ring



theorem exists_fkRectRawHorizontalCrossingComponent_touched_by_closedWalk
    (R : FKRectTorus) (omega : R.Configuration) {x : R.Vertex}
    (p : (fkRectOpenGraph R omega).Walk x x)
    (havoid : ∀ e ∈ p.edges,
      ¬ fkRectCrossesVerticalSeam R e)
    (hwind : (fkRectWalkWinding R p).1 ≠ 0) :
    ∃ C : (fkRectOpenGraph R
        (fkRectForceCutClosed R omega)).ConnectedComponent,
      FKRectRawHorizontalCrossingComponent R
          (fkRectForceCutClosed R omega) C ∧
        ∃ z ∈ p.support,
          (fkRectOpenGraph R
            (fkRectForceCutClosed R omega)).connectedComponentMk z = C := by
  by_contra hnone
  push_neg at hnone
  have hno : ∀ z ∈ p.support,
      ¬ FKRectRawHorizontalCrossingComponent R
        (fkRectForceCutClosed R omega)
          ((fkRectOpenGraph R
            (fkRectForceCutClosed R omega)).connectedComponentMk z) := by
    intro z hz hcross
    exact hnone _ hcross z hz rfl
  have hzero :=
    fkRectWalkWinding_fst_eq_potential_sub_of_supportNoCrossing
      R omega p havoid hno
  simp only [sub_self] at hzero
  exact hwind hzero



theorem exists_fkRectRawHorizontalCrossingComponent_touched_of_winding
    (R : FKRectTorus) (eta : R.Configuration) {x : R.Vertex}
    (p : (fkRectOpenGraph R eta).Walk x x)
    (hwind : (fkRectWalkWinding R p).1 ≠ 0) :
    ∃ C : (fkRectOpenGraph R eta).ConnectedComponent,
      FKRectRawHorizontalCrossingComponent R eta C ∧
        ∃ z ∈ p.support,
          (fkRectOpenGraph R eta).connectedComponentMk z = C := by
  have hedge : ∃ a b : R.Vertex,
      s(a, b) ∈ p.edges ∧ fkRectCrossesHorizontalSeam R s(a, b) := by
    by_contra hnone
    push_neg at hnone
    have hzeroAll : ∀ {u v : R.Vertex}
        (q : (fkRectOpenGraph R eta).Walk u v),
        (∀ a b : R.Vertex, s(a, b) ∈ q.edges →
          ¬ fkRectCrossesHorizontalSeam R s(a, b)) →
        (fkRectWalkWinding R q).1 = 0 := by
      intro u v q hno
      induction q with
      | nil => simp [fkRectWalkWinding]
      | @cons u v w huv q ih =>
          have hhead : ¬ fkRectCrossesHorizontalSeam R s(u, v) :=
            hno u v (by simp)
          have htail : ∀ a b : R.Vertex, s(a, b) ∈ q.edges →
              ¬ fkRectCrossesHorizontalSeam R s(a, b) := by
            intro a b hab
            exact hno a b (by simp [hab])
          simp only [fkRectWalkWinding, Prod.fst]
          rw [fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses
            R u v hhead, ih htail]
          rfl
    have hzero : (fkRectWalkWinding R p).1 = 0 := hzeroAll p hnone
    exact hwind hzero
  obtain ⟨a, b, hab, hseam⟩ := hedge
  have hadj : (fkRectOpenGraph R eta).Adj a b := p.adj_of_mem_edges hab
  have hcomponent :
      (fkRectOpenGraph R eta).connectedComponentMk a =
        (fkRectOpenGraph R eta).connectedComponentMk b :=
    SimpleGraph.ConnectedComponent.sound hadj.reachable
  rw [fkRectCrossesHorizontalSeam_mk] at hseam
  refine ⟨(fkRectOpenGraph R eta).connectedComponentMk a, ?_,
    a, p.fst_mem_support_of_mem_edges hab, rfl⟩
  rcases hseam with ⟨ha0, hblast⟩ | ⟨hb0, halast⟩
  · have haleft : a.1 = fkRectLeftColumn R := by
      apply Fin.ext
      simpa [fkRectLeftColumn] using ha0
    have hbright : b.1 = fkRectRightColumn R := by
      apply Fin.ext
      dsimp [fkRectRightColumn]
      omega
    exact ⟨⟨a.2, by
      congr 1
      exact Prod.ext haleft.symm rfl⟩, ⟨b.2, by
        calc
          (fkRectOpenGraph R eta).connectedComponentMk
              (fkRectRightColumn R, b.2) =
              (fkRectOpenGraph R eta).connectedComponentMk b := by
                congr 1
                exact Prod.ext hbright.symm rfl
          _ = (fkRectOpenGraph R eta).connectedComponentMk a :=
            hcomponent.symm⟩⟩
  · have hbleft : b.1 = fkRectLeftColumn R := by
      apply Fin.ext
      simpa [fkRectLeftColumn] using hb0
    have haright : a.1 = fkRectRightColumn R := by
      apply Fin.ext
      dsimp [fkRectRightColumn]
      omega
    exact ⟨⟨b.2, by
      calc
        (fkRectOpenGraph R eta).connectedComponentMk
            (fkRectLeftColumn R, b.2) =
            (fkRectOpenGraph R eta).connectedComponentMk b := by
              congr 1
              exact Prod.ext hbleft.symm rfl
        _ = (fkRectOpenGraph R eta).connectedComponentMk a :=
          hcomponent.symm⟩, ⟨a.2, by
        congr 1
        exact Prod.ext haright.symm rfl⟩⟩



theorem exists_fkRectRightBoundaryVertex_mem_support_of_winding
    (R : FKRectTorus) (eta : R.Configuration) {x : R.Vertex}
    (p : (fkRectOpenGraph R eta).Walk x x)
    (hwind : (fkRectWalkWinding R p).1 ≠ 0) :
    ∃ y : Fin R.height, (fkRectRightColumn R, y) ∈ p.support := by
  have hedge : ∃ a b : R.Vertex,
      s(a, b) ∈ p.edges ∧ fkRectCrossesHorizontalSeam R s(a, b) := by
    by_contra hnone
    push Not at hnone
    have hzeroAll : ∀ {u v : R.Vertex}
        (q : (fkRectOpenGraph R eta).Walk u v),
        (∀ a b : R.Vertex, s(a, b) ∈ q.edges →
          ¬ fkRectCrossesHorizontalSeam R s(a, b)) →
        (fkRectWalkWinding R q).1 = 0 := by
      intro u v q hno
      induction q with
      | nil => simp [fkRectWalkWinding]
      | @cons u v w huv q ih =>
          have hhead : ¬ fkRectCrossesHorizontalSeam R s(u, v) :=
            hno u v (by simp)
          have htail : ∀ a b : R.Vertex, s(a, b) ∈ q.edges →
              ¬ fkRectCrossesHorizontalSeam R s(a, b) := by
            intro a b hab
            exact hno a b (by simp [hab])
          simp only [fkRectWalkWinding, Prod.fst]
          rw [fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses
            R u v hhead, ih htail]
          rfl
    exact hwind (hzeroAll p hnone)
  obtain ⟨a, b, hab, hseam⟩ := hedge
  rw [fkRectCrossesHorizontalSeam_mk] at hseam
  rcases hseam with ⟨-, hbright⟩ | ⟨-, haright⟩
  · refine ⟨b.2, ?_⟩
    have hb : b = (fkRectRightColumn R, b.2) := by
      apply Prod.ext
      · apply Fin.ext
        dsimp [fkRectRightColumn]
        omega
      · rfl
    rw [← hb]
    exact p.snd_mem_support_of_mem_edges hab
  · refine ⟨a.2, ?_⟩
    have ha : a = (fkRectRightColumn R, a.2) := by
      apply Prod.ext
      · apply Fin.ext
        dsimp [fkRectRightColumn]
        omega
      · rfl
    rw [← ha]
    exact p.fst_mem_support_of_mem_edges hab



theorem fkRectBlackOrbitDisplacement_fst_sub_snd_eq_zero_of_avoidsSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C)
    (d : FKMedialBlackDart R.medialTorus)
    (hdC : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        d.1 = C) :
    (ons_pathDisplacement
      (List.ofFn (fkRectBlackOrbitDirection
        (fkRectConfigurationToMedialPairing R omega) d))).1 -
      (ons_pathDisplacement
        (List.ofFn (fkRectBlackOrbitDirection
          (fkRectConfigurationToMedialPairing R omega) d))).2 = 0 := by
  classical
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  let p := fkMedialBlackBoundaryPerm pairing
  let dir := fkRectBlackOrbitDirection pairing d
  let row : FKMedialBlackDart R.medialTorus → Int := fun e =>
    (fkRectBlackDartShiftedPoint R (0, 0) e).1 -
      (fkRectBlackDartShiftedPoint R (0, 0) e).2
  have hlen : 0 < l.length := fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero l.length := ⟨hlen.ne'⟩
  have hnext (i : Fin l.length) : l.get (i + 1) = p (l.get i) := by
    have hnextList := List.next_getElem l
      (Equiv.Perm.nodup_toList p d) i.val i.isLt
    have happly := Equiv.Perm.next_toList_eq_apply p d (l.get i)
      (List.get_mem l i)
    have happly' : l.next l[i.val] (by
        exact List.getElem_mem (l := l) i.isLt) = p l[i.val] := by
      simpa [l, p, List.get_eq_getElem] using happly
    rw [happly'] at hnextList
    have hiv : (i + 1).val = (i.val + 1) % l.length := by
      simp [Fin.val_add, Nat.add_mod]
    simpa only [List.get_eq_getElem, hiv] using hnextList.symm
  have hcomponent (i : Fin l.length) :
      (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
          (l.get i).1 = C := by
    rw [fkRectBlackOrbitList_get pairing d i]
    rw [fkMedialBlackBoundaryPerm_iterate_val]
    rw [← hdC]
    apply SimpleGraph.ConnectedComponent.sound
    exact (fkMedialBoundaryStep_iterate_reachable pairing d.1 i.val).symm
  have hlocal (i : Fin l.length) :
      2 * ((stepOf (dir i)).1 - (stepOf (dir i)).2) =
        row (l.get (i + 1)) - row (l.get i) := by
    rw [hnext]
    change 2 * ((stepOf
        (fkMedialStrandDirection pairing (l.get i).1)).1 -
      (stepOf (fkMedialStrandDirection pairing (l.get i).1)).2) =
        row (p (l.get i)) - row (l.get i)
    exact fkRectBlackBoundaryStep_row_eq_potential_sub_of_avoidsSeam
      R omega C havoid (l.get i) (hcomponent i)
  have hshift : (∑ i : Fin l.length, row (l.get (i + 1))) =
      ∑ i : Fin l.length, row (l.get i) := by
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin l.length))
      (fun i : Fin l.length => row (l.get i))
  have htwice : 2 *
      ((ons_pathDisplacement (List.ofFn dir)).1 -
        (ons_pathDisplacement (List.ofFn dir)).2) = 0 := by
    rw [fkRectPathDisplacement_row_eq_sum, List.map_ofFn,
      List.sum_ofFn]
    calc
      2 * (∑ i : Fin l.length,
          ((stepOf (dir i)).1 - (stepOf (dir i)).2)) =
          ∑ i : Fin l.length,
            2 * ((stepOf (dir i)).1 - (stepOf (dir i)).2) := by
            rw [Finset.mul_sum]
      _ = ∑ i : Fin l.length,
          (row (l.get (i + 1)) - row (l.get i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hlocal i
      _ = 0 := by
        rw [Finset.sum_sub_distrib, hshift, sub_self]
  change (ons_pathDisplacement (List.ofFn dir)).1 -
      (ons_pathDisplacement (List.ofFn dir)).2 = 0
  omega



theorem fkRectBlackBoundaryPrimalCycleWalk_winding_snd_eq_zero_of_avoidsSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C)
    (d : FKMedialBlackDart R.medialTorus)
    (hdC : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        d.1 = C) :
    (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  let D := ons_pathDisplacement
    (List.ofFn (fkRectBlackOrbitDirection pairing d))
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d :=
    fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have hdart : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  have htrace : fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 n = w := by
    exact (fkRectBlackBoundaryPrimalCycleWalk_winding R omega d).symm
  have hcenter := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R pairing d.1 (0, 0) n
  rw [hdart, htrace] at hcenter
  simp only [add_zero, add_sub_cancel_right] at hcenter
  have hpointW : fkRectBlackBoundaryPointAfter R pairing d n =
      fkRectBlackDartShiftedPoint R w d := by
    unfold fkRectBlackBoundaryPointAfter fkRectBlackDartShiftedPoint
    rw [hblack, hcenter]
  have hpointD := fkRectBlackBoundaryPointAfter_eq_prefix
    R pairing d n
  have hprefix := fkRectBlackOrbitPrefix_length_eq_displacement pairing d
  change fkRectBlackOrbitPrefix pairing d n = D at hprefix
  rw [hprefix] at hpointD
  have hDrow : D.1 - D.2 = 0 := by
    exact fkRectBlackOrbitDisplacement_fst_sub_snd_eq_zero_of_avoidsSeam
      R omega C havoid d hdC
  have heq : fkRectBlackDartShiftedPoint R w d =
      fkRectBlackDartShiftedPoint R (0, 0) d + 2 • D := by
    rw [← fkRectBlackBoundaryPointAfter_zero R pairing d,
      ← hpointW]
    exact hpointD
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  simp only [fkRectBlackDartShiftedPoint, fkRectRefinedDartPoint,
    fkRectSquareDeckTranslation, Prod.fst, Prod.snd, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd, zsmul_eq_mul,
    zero_mul, add_zero] at hx hy
  change w.2 = 0
  have hhalf : (R.height / 2 : Nat) ≠ (0 : Int) := by
    have : 0 < R.height / 2 :=
      Nat.div_pos R.height_gt_two.le (by norm_num)
    exact_mod_cast this.ne'
  have hw : (8 : Int) * (R.height / 2 : Nat) * w.2 =
      2 * (D.1 - D.2) := by
    linear_combination hx - hy
  rw [hDrow] at hw
  simp only [mul_zero] at hw
  exact (mul_eq_zero.mp hw).resolve_left
    (mul_ne_zero (by norm_num) hhalf)



theorem exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (hturn : FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C = 0)
    (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C) :
    ∃ d : FKMedialBlackDart R.medialTorus,
      (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          d.1 = C ∧
        (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 ≠ 0 ∧
        (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 := by
  obtain ⟨d, hdC, hwind⟩ :=
    exists_nonzero_primalBoundaryWinding_of_zeroTurn R omega C hturn
  refine ⟨d, hdC, ?_,
    fkRectBlackBoundaryPrimalCycleWalk_winding_snd_eq_zero_of_avoidsSeam
      R omega C havoid d hdC⟩
  intro hfst
  apply hwind
  apply Prod.ext
  · exact hfst
  · exact fkRectBlackBoundaryPrimalCycleWalk_winding_snd_eq_zero_of_avoidsSeam
      R omega C havoid d hdC

end

end StatMech.FrontierD
