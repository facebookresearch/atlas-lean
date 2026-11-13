/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedOpenWalkCarrier
import Code.FrontierD.FKRectRefinedBoundaryOrbitCarrier
import Code.FrontierD.FKRectRefinedBoundaryOpenPathPotential
import Code.FrontierD.FKRectTorusWindingInsertion











open Finset SimpleGraph

namespace StatMech.FrontierD

open Equiv

noncomputable section

private theorem fkRectCanonicalEdge_squareAxisStep
    (R : FKRectTorus) (e : R.EdgeIndex) :
    FKRectSquareAxisStep
      (fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1)
      (fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2) := by
  unfold FKRectSquareAxisStep
  exact (fkRectLiftedIndexedEdgeEnds_squareStep R e).elim
    Or.inl (fun h => Or.inr (Or.inl h))



theorem fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_scaled_windingDet
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus)
    {G : SimpleGraph R.Vertex} {x : R.Vertex}
    {w : G.Walk x x} {p q : Int × Int}
    {hw : FKRectSquareWalkLift R w p q}
    (C : FKRectRefinedWalkCarrier R hw) :
    fkRectRefinedRawInteraction
        (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d)
        C.coverDarts =
      -(16 * (R.width : Int) * R.height) *
        ((fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).1 *
            (fkRectWalkWinding R w).2 -
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 *
            (fkRectWalkWinding R w).1) := by
  let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d
  have hAbal : IntegralSquareTorusCycle.DartListBalanced A := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation R omega d
  have hCbal : IntegralSquareTorusCycle.DartListBalanced C.coverDarts := by
    apply fkRectSquareCoverDartList_balanced
    exact C.path_translation
  rw [fkRectRefinedRawInteraction_eq_wrap_det A C.coverDarts hAbal hCbal]
  unfold A fkRectCanonicalRefinedBoundaryOrbitCoverDarts
  rw [fkRectSquareCoverDartList_xWrap_eq
    (fkRectRefinedCoverTorus R)
    (fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation R omega d)]
  rw [fkRectSquareCoverDartList_yWrap_eq
    (fkRectRefinedCoverTorus R)
    (fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation R omega d)]
  unfold FKRectRefinedWalkCarrier.coverDarts
  rw [fkRectSquareCoverDartList_xWrap_eq
    (fkRectRefinedCoverTorus R) C.path_translation]
  rw [fkRectSquareCoverDartList_yWrap_eq
    (fkRectRefinedCoverTorus R) C.path_translation]
  rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding]
  unfold FKRectRefinedWalkCarrier.translation
  rw [hw.closed_develop_sub_eq_deck_winding R]
  have hdet := fkRectSquareDeckTranslation_det R
    (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
    (fkRectWalkWinding R w)
  linear_combination 16 * hdet




theorem fkRectConnectedInsertion_boundary_windingIndependent_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
    FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R
          (fkRectConfigurationOfEdges R F)
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))))
      (fkRectWalkWinding R
        (fkRectInsertedFundamentalWalk R F e r)) := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let G := fkRectOpenGraph R omega
  let G' := fkRectOpenGraph R
    (fkRectConfigurationOfEdges R (insert e F))
  let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let a := (fkRectLiftedIndexedEdgeEnds R e).1
  let b := (fkRectLiftedIndexedEdgeEnds R e).2
  let hGG' : G ≤ G' := fkRectOpenGraph_le_insert R F e
  have horient := fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation R e
  by_cases hp : fkRectClosedPairingAtEdge e = true
  · have horient' :
        fkRectLiftedVertex R a = fkRectMedialEastPrimal R e ∧
        fkRectLiftedVertex R b = fkRectMedialWestPrimal R e := by
      simpa [a, b, hp] using horient
    have ha : fkRectLiftedVertex R a = fkRectMedialEastPrimal R e :=
      horient'.1
    have hb : fkRectLiftedVertex R b = fkRectMedialWestPrimal R e :=
      horient'.2
    obtain ⟨q, l, hq, hrlift, hlpath, hlblocks⟩ :=
      exists_fkRectRefinedOpenWalkCarrier R F r b hb
    let z : G'.Walk (fkRectMedialEastPrimal R e)
        (fkRectMedialEastPrimal R e) :=
      .cons (fkRectOpenGraph_insert_adj_medialPrimals R F e)
        (r.mapLe hGG')
    have hedgeDisp : b - a = fkRectDevelopedStep R
        (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e) := by
      have h := fkRectLiftedIndexedEdgeEnds_developedStep R e
      rw [ha, hb] at h
      exact h.symm
    have hzlift : FKRectSquareWalkLift R z a q := by
      exact FKRectSquareWalkLift.cons ha hb hedgeDisp
        (fkRectCanonicalEdge_squareAxisStep R e)
        (hrlift.mapLe R hGG')
    let C : FKRectRefinedWalkCarrier R hzlift :=
      ⟨fkRectRefinedPrimalEdgeDarts R e ++ l,
        (fkRectRefinedPrimalEdgeDarts_path R e).append hlpath⟩
    have hz : fkRectWalkWinding R z =
        fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r) := by
      rw [fkRectInsertedFundamentalWalk_winding]
      dsimp [z]
      simp only [fkRectWalkWinding]
      rw [fkRectWalkWinding_mapLe]
      apply Prod.ext <;> ring
    have htranslation : C.translation =
        (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).1,
          4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).2) := by
      unfold FKRectRefinedWalkCarrier.translation
      rw [hzlift.closed_develop_sub_eq_deck_winding R]
    have hedgeInt :=
      fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_not_reachable
        R F e heF
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
          (fkRectWalkWinding R z) hsep
    have holdInt := hlblocks.repeated_boundary_interaction_eq_zero
      R F d (orderOf (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)))
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
      (fkRectWalkWinding R z)
    have hinteraction : fkRectRefinedRawInteraction
        (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d)
        C.coverDarts ≠ 0 := by
      unfold fkRectCanonicalRefinedBoundaryOrbitCoverDarts
        fkRectCanonicalRefinedBoundaryOrbitDarts
        FKRectRefinedWalkCarrier.coverDarts
      rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
        htranslation]
      unfold fkRectSquareCoverDartList
      rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
        holdInt, add_zero]
      exact hedgeInt
    have hind :=
      (fkRectCanonicalBoundaryOrbitCarrier_interaction_ne_zero_iff
        R omega d C).mp hinteraction
    rw [hz] at hind
    exact hind
  · have hp' : fkRectClosedPairingAtEdge e = false :=
      Bool.eq_false_of_not_eq_true hp
    have horient' :
        fkRectLiftedVertex R a = fkRectMedialWestPrimal R e ∧
        fkRectLiftedVertex R b = fkRectMedialEastPrimal R e := by
      simpa [a, b, hp, hp'] using horient
    have ha : fkRectLiftedVertex R a = fkRectMedialWestPrimal R e :=
      horient'.1
    have hb : fkRectLiftedVertex R b = fkRectMedialEastPrimal R e :=
      horient'.2
    obtain ⟨q, l, hq, hrlift, hlpath, hlblocks⟩ :=
      exists_fkRectRefinedOpenWalkCarrier R F r.reverse b hb
    let z : G'.Walk (fkRectMedialWestPrimal R e)
        (fkRectMedialWestPrimal R e) :=
      .cons (fkRectOpenGraph_insert_adj_medialPrimals R F e).symm
        (r.reverse.mapLe hGG')
    have hedgeDisp : b - a = fkRectDevelopedStep R
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) := by
      have h := fkRectLiftedIndexedEdgeEnds_developedStep R e
      rw [ha, hb] at h
      exact h.symm
    have hzlift : FKRectSquareWalkLift R z a q := by
      exact FKRectSquareWalkLift.cons ha hb hedgeDisp
        (fkRectCanonicalEdge_squareAxisStep R e)
        (hrlift.mapLe R hGG')
    let C : FKRectRefinedWalkCarrier R hzlift :=
      ⟨fkRectRefinedPrimalEdgeDarts R e ++ l,
        (fkRectRefinedPrimalEdgeDarts_path R e).append hlpath⟩
    have hz : fkRectWalkWinding R z =
        (-(fkRectWalkWinding R
          (fkRectInsertedFundamentalWalk R F e r)).1,
          -(fkRectWalkWinding R
          (fkRectInsertedFundamentalWalk R F e r)).2) := by
      rw [fkRectInsertedFundamentalWalk_winding]
      dsimp [z]
      simp only [fkRectWalkWinding]
      rw [fkRectWalkWinding_mapLe, fkRectWalkWinding_reverse,
        fkRectHorizontalSeamIncrement_swap,
        fkRectVerticalSeamIncrement_swap]
      apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> ring
    have htranslation : C.translation =
        (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).1,
          4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).2) := by
      unfold FKRectRefinedWalkCarrier.translation
      rw [hzlift.closed_develop_sub_eq_deck_winding R]
    have hedgeInt :=
      fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_not_reachable
        R F e heF
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
          (fkRectWalkWinding R z) hsep
    have holdInt := hlblocks.repeated_boundary_interaction_eq_zero
      R F d (orderOf (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)))
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
      (fkRectWalkWinding R z)
    have hinteraction : fkRectRefinedRawInteraction
        (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d)
        C.coverDarts ≠ 0 := by
      unfold fkRectCanonicalRefinedBoundaryOrbitCoverDarts
        fkRectCanonicalRefinedBoundaryOrbitDarts
        FKRectRefinedWalkCarrier.coverDarts
      rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
        htranslation]
      unfold fkRectSquareCoverDartList
      rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
        holdInt, add_zero]
      exact hedgeInt
    have hind :=
      (fkRectCanonicalBoundaryOrbitCarrier_interaction_ne_zero_iff
        R omega d C).mp hinteraction
    rw [hz] at hind
    unfold FKRectWindingIndependent at hind ⊢
    intro hzero
    apply hind
    simp only [Prod.fst, Prod.snd]
    have hzero' :
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).1 *
            (fkRectWalkWinding R
              (fkRectInsertedFundamentalWalk R F e r)).2 -
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 *
            (fkRectWalkWinding R
              (fkRectInsertedFundamentalWalk R F e r)).1 = 0 := by
      simpa [omega, d] using hzero
    linear_combination -hzero'




theorem fkRectConnectedInsertion_boundary_windingDet_signs
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
    let omega := fkRectConfigurationOfEdges R F
    let wW := fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    let wE := fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    let z := fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)
    (if fkRectClosedPairingAtEdge e then
        wW.1 * z.2 - wW.2 * z.1 < 0
      else 0 < wW.1 * z.2 - wW.2 * z.1) ∧
    (if fkRectClosedPairingAtEdge e then
        0 < wE.1 * z.2 - wE.2 * z.1
      else wE.1 * z.2 - wE.2 * z.1 < 0) := by
  classical
  dsimp only
  let omega := fkRectConfigurationOfEdges R F
  let G := fkRectOpenGraph R omega
  let G' := fkRectOpenGraph R
    (fkRectConfigurationOfEdges R (insert e F))
  let dW := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let dE := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
  let a := (fkRectLiftedIndexedEdgeEnds R e).1
  let b := (fkRectLiftedIndexedEdgeEnds R e).2
  let hGG' : G ≤ G' := fkRectOpenGraph_le_insert R F e
  have horient := fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation R e
  have hedgeAxis := fkRectCanonicalEdge_squareAxisStep R e
  have hscale : (0 : Int) < 16 * R.width * R.height := by
    have hw : (0 : Int) < R.width := by exact_mod_cast R.width_pos
    have hh : (0 : Int) < R.height := by exact_mod_cast R.height_pos
    positivity
  by_cases hp : fkRectClosedPairingAtEdge e = true
  · have horient' :
        fkRectLiftedVertex R a = fkRectMedialEastPrimal R e ∧
        fkRectLiftedVertex R b = fkRectMedialWestPrimal R e := by
      simpa [a, b, hp] using horient
    have ha := horient'.1
    have hb := horient'.2
    obtain ⟨q, l, hq, hrlift, hlpath, hlblocks⟩ :=
      exists_fkRectRefinedOpenWalkCarrier R F r b hb
    let z : G'.Walk (fkRectMedialEastPrimal R e)
        (fkRectMedialEastPrimal R e) :=
      .cons (fkRectOpenGraph_insert_adj_medialPrimals R F e)
        (r.mapLe hGG')
    have hedgeDisp : b - a = fkRectDevelopedStep R
        (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e) := by
      have h := fkRectLiftedIndexedEdgeEnds_developedStep R e
      rw [ha, hb] at h
      exact h.symm
    have hzlift : FKRectSquareWalkLift R z a q := by
      exact FKRectSquareWalkLift.cons ha hb hedgeDisp hedgeAxis
        (hrlift.mapLe R hGG')
    let C : FKRectRefinedWalkCarrier R hzlift :=
      ⟨fkRectRefinedPrimalEdgeDarts R e ++ l,
        (fkRectRefinedPrimalEdgeDarts_path R e).append hlpath⟩
    have hz : fkRectWalkWinding R z =
        fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r) := by
      rw [fkRectInsertedFundamentalWalk_winding]
      dsimp [z]
      simp only [fkRectWalkWinding]
      rw [fkRectWalkWinding_mapLe]
      apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> ring
    have htranslation : C.translation =
        (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).1,
          4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).2) := by
      unfold FKRectRefinedWalkCarrier.translation
      rw [hzlift.closed_develop_sub_eq_deck_winding R]
    have hWedge :=
      fkRectRefinedRawInteraction_repeated_west_boundary_edge_pos
        R F e heF
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega dW))
          (fkRectWalkWinding R z) hsep
    have hEedge :=
      fkRectRefinedRawInteraction_repeated_east_boundary_edge_neg
        R F e heF
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega dE))
          (fkRectWalkWinding R z) hsep
    have hWold := hlblocks.repeated_boundary_interaction_eq_zero
      R F dW (orderOf (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)))
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega dW))
      (fkRectWalkWinding R z)
    have hEold := hlblocks.repeated_boundary_interaction_eq_zero
      R F dE (orderOf (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)))
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega dE))
      (fkRectWalkWinding R z)
    have hW : 0 < fkRectRefinedRawInteraction
        (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dW)
        C.coverDarts := by
      unfold fkRectCanonicalRefinedBoundaryOrbitCoverDarts
        fkRectCanonicalRefinedBoundaryOrbitDarts
        FKRectRefinedWalkCarrier.coverDarts
      rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
        htranslation]
      unfold fkRectSquareCoverDartList
      rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
        hWold, add_zero]
      exact hWedge
    have hE : fkRectRefinedRawInteraction
        (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dE)
        C.coverDarts < 0 := by
      unfold fkRectCanonicalRefinedBoundaryOrbitCoverDarts
        fkRectCanonicalRefinedBoundaryOrbitDarts
        FKRectRefinedWalkCarrier.coverDarts
      rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
        htranslation]
      unfold fkRectSquareCoverDartList
      rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
        hEold, add_zero]
      exact hEedge
    have hdetW :=
      fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_scaled_windingDet
        R omega dW C
    have hdetE :=
      fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_scaled_windingDet
        R omega dE C
    rw [hz] at hdetW hdetE
    rw [if_pos hp, if_pos hp]
    constructor <;> nlinarith
  · have hp' : fkRectClosedPairingAtEdge e = false :=
      Bool.eq_false_of_not_eq_true hp
    have horient' :
        fkRectLiftedVertex R a = fkRectMedialWestPrimal R e ∧
        fkRectLiftedVertex R b = fkRectMedialEastPrimal R e := by
      simpa [a, b, hp, hp'] using horient
    have ha := horient'.1
    have hb := horient'.2
    obtain ⟨q, l, hq, hrlift, hlpath, hlblocks⟩ :=
      exists_fkRectRefinedOpenWalkCarrier R F r.reverse b hb
    let z : G'.Walk (fkRectMedialWestPrimal R e)
        (fkRectMedialWestPrimal R e) :=
      .cons (fkRectOpenGraph_insert_adj_medialPrimals R F e).symm
        (r.reverse.mapLe hGG')
    have hedgeDisp : b - a = fkRectDevelopedStep R
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) := by
      have h := fkRectLiftedIndexedEdgeEnds_developedStep R e
      rw [ha, hb] at h
      exact h.symm
    have hzlift : FKRectSquareWalkLift R z a q := by
      exact FKRectSquareWalkLift.cons ha hb hedgeDisp hedgeAxis
        (hrlift.mapLe R hGG')
    let C : FKRectRefinedWalkCarrier R hzlift :=
      ⟨fkRectRefinedPrimalEdgeDarts R e ++ l,
        (fkRectRefinedPrimalEdgeDarts_path R e).append hlpath⟩
    have hz : fkRectWalkWinding R z =
        -(fkRectWalkWinding R
          (fkRectInsertedFundamentalWalk R F e r)) := by
      rw [fkRectInsertedFundamentalWalk_winding]
      dsimp [z]
      simp only [fkRectWalkWinding]
      rw [fkRectWalkWinding_mapLe, fkRectWalkWinding_reverse,
        fkRectHorizontalSeamIncrement_swap,
        fkRectVerticalSeamIncrement_swap]
      apply Prod.ext <;> ring
    have htranslation : C.translation =
        (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).1,
          4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).2) := by
      unfold FKRectRefinedWalkCarrier.translation
      rw [hzlift.closed_develop_sub_eq_deck_winding R]
    have hWedge :=
      fkRectRefinedRawInteraction_repeated_west_boundary_edge_pos
        R F e heF
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega dW))
          (fkRectWalkWinding R z) hsep
    have hEedge :=
      fkRectRefinedRawInteraction_repeated_east_boundary_edge_neg
        R F e heF
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega dE))
          (fkRectWalkWinding R z) hsep
    have hWold := hlblocks.repeated_boundary_interaction_eq_zero
      R F dW (orderOf (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)))
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega dW))
      (fkRectWalkWinding R z)
    have hEold := hlblocks.repeated_boundary_interaction_eq_zero
      R F dE (orderOf (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)))
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega dE))
      (fkRectWalkWinding R z)
    have hW : 0 < fkRectRefinedRawInteraction
        (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dW)
        C.coverDarts := by
      unfold fkRectCanonicalRefinedBoundaryOrbitCoverDarts
        fkRectCanonicalRefinedBoundaryOrbitDarts
        FKRectRefinedWalkCarrier.coverDarts
      rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
        htranslation]
      unfold fkRectSquareCoverDartList
      rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
        hWold, add_zero]
      exact hWedge
    have hE : fkRectRefinedRawInteraction
        (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dE)
        C.coverDarts < 0 := by
      unfold fkRectCanonicalRefinedBoundaryOrbitCoverDarts
        fkRectCanonicalRefinedBoundaryOrbitDarts
        FKRectRefinedWalkCarrier.coverDarts
      rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
        htranslation]
      unfold fkRectSquareCoverDartList
      rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
        hEold, add_zero]
      exact hEedge
    have hdetW :=
      fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_scaled_windingDet
        R omega dW C
    have hdetE :=
      fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_scaled_windingDet
        R omega dE C
    rw [hz] at hdetW hdetE
    rw [if_neg hp, if_neg hp]
    simp only [Prod.fst_neg, Prod.snd_neg] at hdetW hdetE
    constructor <;> nlinarith

end

end StatMech.FrontierD
