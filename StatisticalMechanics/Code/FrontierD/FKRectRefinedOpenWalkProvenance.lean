/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedOpenWalkCarrier










namespace StatMech.FrontierD

noncomputable section



inductive FKRectRefinedOpenWalkBlocksAlong
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    {x y : R.Vertex} ->
      (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x y ->
      (Int × Int) -> (Int × Int) ->
      List FKRectIntegralSquareDart -> Prop
  | nil {x : R.Vertex} (p : Int × Int)
      (hp : fkRectLiftedVertex R p = x) :
      FKRectRefinedOpenWalkBlocksAlong R F
        ((.nil : (fkRectOpenGraph R
          (fkRectConfigurationOfEdges R F)).Walk x x)) p p []
  | consForward {x y z : R.Vertex}
      (hxy : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Adj x y)
      {w : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk y z}
      (e : R.EdgeIndex) (u : Int × Int) (he : e ∈ F)
      {p q r : Int × Int}
      (hp : fkRectLiftedVertex R p = x)
      (hq : fkRectLiftedVertex R q = y)
      (hpDeck : p =
        ((fkRectLiftedIndexedEdgeEnds R e).1.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R e).1.2 +
            (R.height : Int) * u.2))
      (hqDeck : q =
        ((fkRectLiftedIndexedEdgeEnds R e).2.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R e).2.2 +
            (R.height : Int) * u.2))
      (hdisp : q - p = fkRectDevelopedStep R x y)
      (haxis : FKRectSquareAxisStep
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q))
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedOpenWalkBlocksAlong R F w q r l) :
      FKRectRefinedOpenWalkBlocksAlong R F (.cons hxy w) p r
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate
            (4 * (fkRectSquareDeckTranslation R u).1,
              4 * (fkRectSquareDeckTranslation R u).2)) ++ l)
  | consReverse {x y z : R.Vertex}
      (hxy : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Adj x y)
      {w : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk y z}
      (e : R.EdgeIndex) (u : Int × Int) (he : e ∈ F)
      {p q r : Int × Int}
      (hp : fkRectLiftedVertex R p = x)
      (hq : fkRectLiftedVertex R q = y)
      (hpDeck : p =
        ((fkRectLiftedIndexedEdgeEnds R e).2.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R e).2.2 +
            (R.height : Int) * u.2))
      (hqDeck : q =
        ((fkRectLiftedIndexedEdgeEnds R e).1.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R e).1.2 +
            (R.height : Int) * u.2))
      (hdisp : q - p = fkRectDevelopedStep R x y)
      (haxis : FKRectSquareAxisStep
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q))
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedOpenWalkBlocksAlong R F w q r l) :
      FKRectRefinedOpenWalkBlocksAlong R F (.cons hxy w) p r
        ((fkRectIntegralSquareDartListReverse
          (fkRectRefinedPrimalEdgeDarts R e)).map
            (fkRectIntegralSquareDartTranslate
              (4 * (fkRectSquareDeckTranslation R u).1,
                4 * (fkRectSquareDeckTranslation R u).2)) ++ l)



theorem FKRectRefinedOpenWalkBlocksAlong.toOpenEdgeBlocks
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {x y : R.Vertex}
    {w : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk x y}
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectRefinedOpenWalkBlocksAlong R F w p q l) :
    FKRectRefinedOpenEdgeBlocks R F l := by
  induction h with
  | nil _ _ => exact .nil
  | consForward _ e u he _ _ _ _ _ _ _ ih =>
      exact .consForward e u he ih
  | consReverse _ e u he _ _ _ _ _ _ _ ih =>
      exact .consReverse e u he ih



theorem FKRectRefinedOpenWalkBlocksAlong.toSquareWalkLift
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {x y : R.Vertex}
    {w : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk x y}
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectRefinedOpenWalkBlocksAlong R F w p q l) :
    FKRectSquareWalkLift R w p q := by
  induction h with
  | nil p hp => exact .nil p hp
  | consForward _ _ _ _ hp hq _ _ hdisp haxis _ ih =>
      exact .cons hp hq hdisp haxis ih
  | consReverse _ _ _ _ hp hq _ _ hdisp haxis _ ih =>
      exact .cons hp hq hdisp haxis ih

private theorem fkRectRefinedScale_develop_add_period_provenance
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



theorem exists_fkRectRefinedOpenWalkCarrierAlong
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
      FKRectRefinedOpenEdgeBlocks R F l ∧
      FKRectRefinedOpenWalkBlocksAlong R F w p q l := by
  induction w generalizing p with
  | nil =>
      exact ⟨p, [], hp, FKRectSquareWalkLift.nil p hp,
        FKRectIntegralSquareDartPath.nil _,
        FKRectRefinedOpenEdgeBlocks.nil,
        FKRectRefinedOpenWalkBlocksAlong.nil p hp⟩
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
        obtain ⟨r, l, hr, hllift, hlpath, hlblocks, hlalong⟩ := ih q hq
        let t : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R u).1,
            4 * (fkRectSquareDeckTranslation R u).2)
        have hedgePath := (fkRectRefinedPrimalEdgeDarts_path R e).translate t
        have hstart : fkRectRefinedPrimalEdgeStart R e =
            fkRectRefinedScalePoint (fkRectSquareDevelopPoint a) := by rfl
        have hend : fkRectRefinedPrimalEdgeEnd R e =
            fkRectRefinedScalePoint (fkRectSquareDevelopPoint b) := by rfl
        rw [hstart, hend,
          ← fkRectRefinedScale_develop_add_period_provenance R a u,
          ← fkRectRefinedScale_develop_add_period_provenance R b u] at hedgePath
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
        have hpDeck : p =
            ((fkRectLiftedIndexedEdgeEnds R e).1.1 +
                (R.width : Int) * u.1,
              (fkRectLiftedIndexedEdgeEnds R e).1.2 +
                (R.height : Int) * u.2) := by
          simpa [a] using hu
        have hqDeck : q =
            ((fkRectLiftedIndexedEdgeEnds R e).2.1 +
                (R.width : Int) * u.1,
              (fkRectLiftedIndexedEdgeEnds R e).2.2 +
                (R.height : Int) * u.2) := by
          rfl
        let hxy' : (fkRectOpenGraph R
            (fkRectConfigurationOfEdges R F)).Adj x y :=
          ⟨e, heopen, hedge⟩
        let hwhole := FKRectSquareWalkLift.cons
          (hxy := hxy') hp hq hdisp haxis hllift
        refine ⟨r, _ ++ l, hr, hwhole, hedgePath.append hlpath,
          FKRectRefinedOpenEdgeBlocks.consForward e u heF hlblocks, ?_⟩
        exact FKRectRefinedOpenWalkBlocksAlong.consForward hxy' e u heF
          hp hq hpDeck hqDeck hdisp haxis hlalong
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
        obtain ⟨r, l, hr, hllift, hlpath, hlblocks, hlalong⟩ := ih q hq
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
          ← fkRectRefinedScale_develop_add_period_provenance R a u,
          ← fkRectRefinedScale_develop_add_period_provenance R b u] at hedgePath
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
        have hpDeck : p =
            ((fkRectLiftedIndexedEdgeEnds R e).2.1 +
                (R.width : Int) * u.1,
              (fkRectLiftedIndexedEdgeEnds R e).2.2 +
                (R.height : Int) * u.2) := by
          simpa [b] using hu
        have hqDeck : q =
            ((fkRectLiftedIndexedEdgeEnds R e).1.1 +
                (R.width : Int) * u.1,
              (fkRectLiftedIndexedEdgeEnds R e).1.2 +
                (R.height : Int) * u.2) := by
          rfl
        let hxy' : (fkRectOpenGraph R
            (fkRectConfigurationOfEdges R F)).Adj x y :=
          ⟨e, heopen, hedge⟩
        let hwhole := FKRectSquareWalkLift.cons
          (hxy := hxy') hp hq hdisp haxis hllift
        refine ⟨r, _ ++ l, hr, hwhole, hedgePath.append hlpath,
          FKRectRefinedOpenEdgeBlocks.consReverse e u heF hlblocks, ?_⟩
        exact FKRectRefinedOpenWalkBlocksAlong.consReverse hxy' e u heF
          hp hq hpDeck hqDeck hdisp haxis hlalong

end

end StatMech.FrontierD
