/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedPathReversal
import Code.FrontierD.FKRectRefinedRepeatedAppend









namespace StatMech.FrontierD

noncomputable section



inductive FKRectRefinedOpenEdgeBlocks
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    List FKRectIntegralSquareDart -> Prop
  | nil : FKRectRefinedOpenEdgeBlocks R F []
  | consForward (e : R.EdgeIndex) (u : Int × Int) (he : e ∈ F)
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedOpenEdgeBlocks R F l) :
      FKRectRefinedOpenEdgeBlocks R F
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate
            (4 * (fkRectSquareDeckTranslation R u).1,
              4 * (fkRectSquareDeckTranslation R u).2)) ++ l)
  | consReverse (e : R.EdgeIndex) (u : Int × Int) (he : e ∈ F)
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedOpenEdgeBlocks R F l) :
      FKRectRefinedOpenEdgeBlocks R F
        ((fkRectIntegralSquareDartListReverse
          (fkRectRefinedPrimalEdgeDarts R e)).map
            (fkRectIntegralSquareDartTranslate
              (4 * (fkRectSquareDeckTranslation R u).1,
              4 * (fkRectSquareDeckTranslation R u).2)) ++ l)



theorem FKRectSquareWalkLift.mapLe
    (R : FKRectTorus) {G H : SimpleGraph R.Vertex} (hGH : G ≤ H)
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    FKRectSquareWalkLift R (w.mapLe hGH) p q := by
  induction h with
  | nil p hp => exact FKRectSquareWalkLift.nil p hp
  | cons hp hq hdisp haxis tail ih =>
      exact FKRectSquareWalkLift.cons hp hq hdisp haxis ih

private theorem fkRectRefinedScale_develop_add_period
    (R : FKRectTorus) (p : Int × Int) (u : Int × Int) :
    fkRectRefinedScalePoint
        (fkRectSquareDevelopPoint
          (p.1 + (R.width : Int) * u.1,
            p.2 + (R.height : Int) * u.2)) =
      ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 +
          4 * (fkRectSquareDeckTranslation R u).2) := by
  have h := fkRectSquareDevelopPoint_add_period R p u
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;>
    simp [fkRectRefinedScalePoint] at hx hy ⊢ <;> linarith



theorem exists_fkRectRefinedOpenWalkCarrier
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {x y : R.Vertex}
    (w : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk x y)
    (p : Int × Int) (hp : fkRectLiftedVertex R p = x) :
    ∃ q : Int × Int, ∃ l : List FKRectIntegralSquareDart,
      fkRectLiftedVertex R q = y ∧
      FKRectSquareWalkLift R w p q ∧
      FKRectIntegralSquareDartPath
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) l ∧
      FKRectRefinedOpenEdgeBlocks R F l := by
  induction w generalizing p with
  | nil =>
      exact ⟨p, [], hp, FKRectSquareWalkLift.nil p hp,
        FKRectIntegralSquareDartPath.nil _,
        FKRectRefinedOpenEdgeBlocks.nil⟩
  | @cons x y z hxy w ih =>
      obtain ⟨e, heopen, hedge⟩ := hxy
      have heF : e ∈ F := by
        rw [fkRectConfigurationOfEdges_apply] at heopen
        exact heopen
      let a := (fkRectLiftedIndexedEdgeEnds R e).1
      let b := (fkRectLiftedIndexedEdgeEnds R e).2
      have hcanonical := fkRectLiftedIndexedEdgeEnds_project R e
      have hpairs :
          s(fkRectLiftedVertex R a, fkRectLiftedVertex R b) = s(x, y) :=
        hcanonical.symm.trans hedge
      rcases Sym2.eq_iff.mp hpairs with horient | horient
      · have hpa : fkRectLiftedVertex R p = fkRectLiftedVertex R a :=
          hp.trans horient.1.symm
        obtain ⟨u, hu⟩ :=
          (fkRectLiftedVertex_eq_iff_exists_period R p a).mp hpa
        let q : Int × Int :=
          (b.1 + (R.width : Int) * u.1,
            b.2 + (R.height : Int) * u.2)
        have hq : fkRectLiftedVertex R q = y := by
          have hqb : fkRectLiftedVertex R q = fkRectLiftedVertex R b :=
            (fkRectLiftedVertex_eq_iff_exists_period R q b).mpr ⟨u, rfl⟩
          exact hqb.trans horient.2
        obtain ⟨r, l, hr, hllift, hlpath, hlblocks⟩ := ih q hq
        let t : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R u).1,
            4 * (fkRectSquareDeckTranslation R u).2)
        have hedgePath := (fkRectRefinedPrimalEdgeDarts_path R e).translate t
        have hstart : fkRectRefinedPrimalEdgeStart R e =
            fkRectRefinedScalePoint (fkRectSquareDevelopPoint a) := by rfl
        have hend : fkRectRefinedPrimalEdgeEnd R e =
            fkRectRefinedScalePoint (fkRectSquareDevelopPoint b) := by rfl
        rw [hstart, hend,
          ← fkRectRefinedScale_develop_add_period R a u,
          ← fkRectRefinedScale_develop_add_period R b u] at hedgePath
        rw [← hu] at hedgePath
        have hdisp : q - p = fkRectDevelopedStep R x y := by
          rw [← horient.1, ← horient.2,
            fkRectLiftedIndexedEdgeEnds_developedStep R e]
          dsimp [q]
          rw [hu]
          apply Prod.ext <;> simp <;> ring
        have haxis : FKRectSquareAxisStep
            (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) := by
          rw [hu]
          dsimp [q]
          unfold FKRectSquareAxisStep
          rw [fkRectSquareDevelopPoint_sub_add_period R a b u]
          exact (fkRectLiftedIndexedEdgeEnds_squareStep R e).elim
            Or.inl (fun h => Or.inr (Or.inl h))
        refine ⟨r, _ ++ l, hr,
          FKRectSquareWalkLift.cons hp hq hdisp haxis hllift,
          hedgePath.append hlpath, ?_⟩
        exact FKRectRefinedOpenEdgeBlocks.consForward e u heF hlblocks
      · have hpb : fkRectLiftedVertex R p = fkRectLiftedVertex R b :=
          hp.trans horient.2.symm
        obtain ⟨u, hu⟩ :=
          (fkRectLiftedVertex_eq_iff_exists_period R p b).mp hpb
        let q : Int × Int :=
          (a.1 + (R.width : Int) * u.1,
            a.2 + (R.height : Int) * u.2)
        have hq : fkRectLiftedVertex R q = y := by
          have hqa : fkRectLiftedVertex R q = fkRectLiftedVertex R a :=
            (fkRectLiftedVertex_eq_iff_exists_period R q a).mpr ⟨u, rfl⟩
          exact hqa.trans horient.1
        obtain ⟨r, l, hr, hllift, hlpath, hlblocks⟩ := ih q hq
        let t : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R u).1,
            4 * (fkRectSquareDeckTranslation R u).2)
        have hedgePath :=
          (fkRectRefinedPrimalEdgeDarts_path R e).reverse.translate t
        have hstart : fkRectRefinedPrimalEdgeStart R e =
            fkRectRefinedScalePoint (fkRectSquareDevelopPoint a) := by rfl
        have hend : fkRectRefinedPrimalEdgeEnd R e =
            fkRectRefinedScalePoint (fkRectSquareDevelopPoint b) := by rfl
        rw [hstart, hend,
          ← fkRectRefinedScale_develop_add_period R a u,
          ← fkRectRefinedScale_develop_add_period R b u] at hedgePath
        rw [← hu] at hedgePath
        have hdisp : q - p = fkRectDevelopedStep R x y := by
          rw [← horient.2, ← horient.1,
            fkRectDevelopedStep_swap,
            fkRectLiftedIndexedEdgeEnds_developedStep R e]
          dsimp [q]
          rw [hu]
          apply Prod.ext <;> simp <;> ring
        have haxis : FKRectSquareAxisStep
            (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) := by
          rw [hu]
          dsimp [q]
          apply FKRectSquareAxisStep.symm
          unfold FKRectSquareAxisStep
          rw [fkRectSquareDevelopPoint_sub_add_period R a b u]
          exact (fkRectLiftedIndexedEdgeEnds_squareStep R e).elim
            Or.inl (fun h => Or.inr (Or.inl h))
        refine ⟨r, _ ++ l, hr,
          FKRectSquareWalkLift.cons hp hq hdisp haxis hllift,
          hedgePath.append hlpath, ?_⟩
        exact FKRectRefinedOpenEdgeBlocks.consReverse e u heF hlblocks

private theorem fkRectTranslateMap_comp
    (l : List FKRectIntegralSquareDart) (a b : Int × Int) :
    ((l.map (fkRectIntegralSquareDartTranslate a)).map
        (fkRectIntegralSquareDartTranslate b)) =
      l.map (fkRectIntegralSquareDartTranslate
        (a.1 + b.1, a.2 + b.2)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro d hd
  simp only [Function.comp_apply]
  rw [fkRectIntegralSquareDartTranslate_comp]

private theorem fkRectRefinedRawInteraction_repeated_boundary_openEdgeDeck_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∈ F) (d : FKMedialDart R.medialTorus) (n : Nat)
    (s w z : Int × Int) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let S : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R s).1,
        4 * (fkRectSquareDeckTranslation R s).2)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    let V : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R z).1,
        4 * (fkRectSquareDeckTranslation R z).2)
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRepeatTranslatedDartPath
          ((fkRectRefinedPrimalEdgeDarts R e).map
            (fkRectIntegralSquareDartTranslate S)) V L).map
              (fkRectIntegralSquareDartMod L)) = 0 := by
  classical
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let S : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R s).1,
      4 * (fkRectSquareDeckTranslation R s).2)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  let V : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R z).1,
      4 * (fkRectSquareDeckTranslation R z).2)
  change fkRectRefinedRawInteraction
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedBoundaryDarts pairing d c n) U L).map
          (fkRectIntegralSquareDartMod L))
      ((fkRectRepeatTranslatedDartPath
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate S)) V L).map
            (fkRectIntegralSquareDartMod L)) = 0
  rw [fkRectRefinedRawInteraction_repeatTranslated_both]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [fkRectTranslateMap_comp]
  let u : Int × Int :=
    ((i : Int) * w.1 - s.1 - (j : Int) * z.1,
      (i : Int) * w.2 - s.2 - (j : Int) * z.2)
  apply fkRectRefinedRawInteraction_translated_boundary_openEdge_eq_zero
    R F e heF d n (fkRectNatScale i U)
      (S.1 + (fkRectNatScale j V).1,
        S.2 + (fkRectNatScale j V).2) u
  apply Prod.ext <;>
    simp [u, S, U, V, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring

private theorem fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverseDeck_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∈ F) (d : FKMedialDart R.medialTorus) (n : Nat)
    (s w z : Int × Int) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let S : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R s).1,
        4 * (fkRectSquareDeckTranslation R s).2)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    let V : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R z).1,
        4 * (fkRectSquareDeckTranslation R z).2)
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRepeatTranslatedDartPath
          ((fkRectIntegralSquareDartListReverse
            (fkRectRefinedPrimalEdgeDarts R e)).map
              (fkRectIntegralSquareDartTranslate S)) V L).map
                (fkRectIntegralSquareDartMod L)) = 0 := by
  classical
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let S : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R s).1,
      4 * (fkRectSquareDeckTranslation R s).2)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  let V : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R z).1,
      4 * (fkRectSquareDeckTranslation R z).2)
  change fkRectRefinedRawInteraction
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedBoundaryDarts pairing d c n) U L).map
          (fkRectIntegralSquareDartMod L))
      ((fkRectRepeatTranslatedDartPath
        ((fkRectIntegralSquareDartListReverse
          (fkRectRefinedPrimalEdgeDarts R e)).map
            (fkRectIntegralSquareDartTranslate S)) V L).map
              (fkRectIntegralSquareDartMod L)) = 0
  rw [fkRectRefinedRawInteraction_repeatTranslated_both]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [fkRectTranslateMap_comp]
  let u : Int × Int :=
    ((i : Int) * w.1 - s.1 - (j : Int) * z.1,
      (i : Int) * w.2 - s.2 - (j : Int) * z.2)
  apply
    fkRectRefinedRawInteraction_translated_boundary_openEdgeReverse_eq_zero
      R F e heF d n (fkRectNatScale i U)
        (S.1 + (fkRectNatScale j V).1,
          S.2 + (fkRectNatScale j V).2) u
  apply Prod.ext <;>
    simp [u, S, U, V, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring




theorem FKRectRefinedOpenEdgeBlocks.repeated_boundary_interaction_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {l : List FKRectIntegralSquareDart}
    (hl : FKRectRefinedOpenEdgeBlocks R F l)
    (d : FKMedialDart R.medialTorus) (n : Nat) (w z : Int × Int) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    let V : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R z).1,
        4 * (fkRectSquareDeckTranslation R z).2)
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRepeatTranslatedDartPath l V L).map
          (fkRectIntegralSquareDartMod L)) = 0 := by
  induction hl with
  | nil =>
      dsimp only
      have hempty (V : Int × Int) (m : Nat) :
          fkRectRepeatTranslatedDartPath [] V m = [] := by
        induction m with
        | zero => rfl
        | succ m ih => simp [fkRectRepeatTranslatedDartPath, ih]
      rw [hempty]
      simp [fkRectRefinedRawInteraction]
  | @consForward e s he l tail ih =>
      dsimp only
      rw [fkRectRefinedRawInteraction_repeatTranslated_append_right]
      rw [fkRectRefinedRawInteraction_repeated_boundary_openEdgeDeck_eq_zero
        R F e he d n s w z, ih, add_zero]
  | @consReverse e s he l tail ih =>
      dsimp only
      rw [fkRectRefinedRawInteraction_repeatTranslated_append_right]
      rw [fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverseDeck_eq_zero
        R F e he d n s w z, ih, add_zero]

end

end StatMech.FrontierD
