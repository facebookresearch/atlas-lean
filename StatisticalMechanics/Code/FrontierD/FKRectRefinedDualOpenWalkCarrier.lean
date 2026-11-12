/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedDualEdgeCarrier
import Code.FrontierD.FKRectRefinedPathReversal








namespace StatMech.FrontierD

noncomputable section


def fkRectRefinedDualScalePoint (p : Int × Int) : Int × Int :=
  (4 * p.1 + 2, 4 * p.2 + 2)



inductive FKRectRefinedDualOpenEdgeBlocks
    (R : FKRectTorus) (omega : R.Configuration) :
    List FKRectIntegralSquareDart -> Prop
  | nil : FKRectRefinedDualOpenEdgeBlocks R omega []
  | consForward (d : R.EdgeIndex) (u : Int × Int)
      (hd : fkRectDualConfigurationEquiv R omega d = true)
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedDualOpenEdgeBlocks R omega l) :
      FKRectRefinedDualOpenEdgeBlocks R omega
        ((fkRectRefinedDualEdgeDarts R d).map
          (fkRectIntegralSquareDartTranslate
            (4 * (fkRectSquareDeckTranslation R u).1,
              4 * (fkRectSquareDeckTranslation R u).2)) ++ l)
  | consReverse (d : R.EdgeIndex) (u : Int × Int)
      (hd : fkRectDualConfigurationEquiv R omega d = true)
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedDualOpenEdgeBlocks R omega l) :
      FKRectRefinedDualOpenEdgeBlocks R omega
        ((fkRectIntegralSquareDartListReverse
          (fkRectRefinedDualEdgeDarts R d)).map
            (fkRectIntegralSquareDartTranslate
              (4 * (fkRectSquareDeckTranslation R u).1,
                4 * (fkRectSquareDeckTranslation R u).2)) ++ l)



inductive FKRectRefinedDualOpenWalkBlocksAlong
    (R : FKRectTorus) (omega : R.Configuration) :
    {x y : R.Vertex} ->
      (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R omega)).Walk x y ->
      (Int × Int) -> (Int × Int) ->
      List FKRectIntegralSquareDart -> Prop
  | nil {x : R.Vertex} (p : Int × Int)
      (hp : fkRectLiftedVertex R p = x) :
      FKRectRefinedDualOpenWalkBlocksAlong R omega
        ((.nil : (fkRectOpenGraph R
          (fkRectDualConfigurationEquiv R omega)).Walk x x)) p p []
  | consForward {x y z : R.Vertex}
      (hxy : (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R omega)).Adj x y)
      {w : (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R omega)).Walk y z}
      (d : R.EdgeIndex) (u : Int × Int)
      (hd : fkRectDualConfigurationEquiv R omega d = true)
      {p q r : Int × Int}
      (hp : fkRectLiftedVertex R p = x)
      (hq : fkRectLiftedVertex R q = y)
      (hpDeck : p =
        ((fkRectLiftedIndexedEdgeEnds R d).1.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R d).1.2 +
            (R.height : Int) * u.2))
      (hqDeck : q =
        ((fkRectLiftedIndexedEdgeEnds R d).2.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R d).2.2 +
            (R.height : Int) * u.2))
      (hdisp : q - p = fkRectDevelopedStep R x y)
      (haxis : FKRectSquareAxisStep
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q))
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedDualOpenWalkBlocksAlong R omega w q r l) :
      FKRectRefinedDualOpenWalkBlocksAlong R omega (.cons hxy w) p r
        ((fkRectRefinedDualEdgeDarts R d).map
          (fkRectIntegralSquareDartTranslate
            (4 * (fkRectSquareDeckTranslation R u).1,
              4 * (fkRectSquareDeckTranslation R u).2)) ++ l)
  | consReverse {x y z : R.Vertex}
      (hxy : (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R omega)).Adj x y)
      {w : (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R omega)).Walk y z}
      (d : R.EdgeIndex) (u : Int × Int)
      (hd : fkRectDualConfigurationEquiv R omega d = true)
      {p q r : Int × Int}
      (hp : fkRectLiftedVertex R p = x)
      (hq : fkRectLiftedVertex R q = y)
      (hpDeck : p =
        ((fkRectLiftedIndexedEdgeEnds R d).2.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R d).2.2 +
            (R.height : Int) * u.2))
      (hqDeck : q =
        ((fkRectLiftedIndexedEdgeEnds R d).1.1 +
            (R.width : Int) * u.1,
          (fkRectLiftedIndexedEdgeEnds R d).1.2 +
            (R.height : Int) * u.2))
      (hdisp : q - p = fkRectDevelopedStep R x y)
      (haxis : FKRectSquareAxisStep
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q))
      {l : List FKRectIntegralSquareDart}
      (tail : FKRectRefinedDualOpenWalkBlocksAlong R omega w q r l) :
      FKRectRefinedDualOpenWalkBlocksAlong R omega (.cons hxy w) p r
        ((fkRectIntegralSquareDartListReverse
          (fkRectRefinedDualEdgeDarts R d)).map
            (fkRectIntegralSquareDartTranslate
              (4 * (fkRectSquareDeckTranslation R u).1,
                4 * (fkRectSquareDeckTranslation R u).2)) ++ l)

theorem FKRectRefinedDualOpenWalkBlocksAlong.toOpenEdgeBlocks
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    {w : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).Walk x y}
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectRefinedDualOpenWalkBlocksAlong R omega w p q l) :
    FKRectRefinedDualOpenEdgeBlocks R omega l := by
  induction h with
  | nil _ _ => exact .nil
  | consForward _ d u hd _ _ _ _ _ _ _ ih =>
      exact .consForward d u hd ih
  | consReverse _ d u hd _ _ _ _ _ _ _ ih =>
      exact .consReverse d u hd ih

theorem FKRectRefinedDualOpenWalkBlocksAlong.toSquareWalkLift
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    {w : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).Walk x y}
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectRefinedDualOpenWalkBlocksAlong R omega w p q l) :
    FKRectSquareWalkLift R w p q := by
  induction h with
  | nil p hp => exact .nil p hp
  | consForward _ _ _ _ hp hq _ _ hdisp haxis _ ih =>
      exact .cons hp hq hdisp haxis ih
  | consReverse _ _ _ _ hp hq _ _ hdisp haxis _ ih =>
      exact .cons hp hq hdisp haxis ih

private theorem fkRectRefinedDualScale_develop_add_period
    (R : FKRectTorus) (p : Int × Int) (u : Int × Int) :
    fkRectRefinedDualScalePoint
        (fkRectSquareDevelopPoint
          (p.1 + (R.width : Int) * u.1,
            p.2 + (R.height : Int) * u.2)) =
      ((fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).2 +
          4 * (fkRectSquareDeckTranslation R u).2) := by
  have h := fkRectSquareDevelopPoint_add_period R p u
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;>
    simp [fkRectRefinedDualScalePoint] at hx hy ⊢ <;> linarith



theorem exists_fkRectRefinedDualOpenWalkCarrierAlong
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    (w : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).Walk x y)
    (p : Int × Int) (hp : fkRectLiftedVertex R p = x) :
    ∃ q : Int × Int, ∃ l : List FKRectIntegralSquareDart,
      fkRectLiftedVertex R q = y ∧
      FKRectSquareWalkLift R w p q ∧
      FKRectIntegralSquareDartPath
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q)) l ∧
      FKRectRefinedDualOpenEdgeBlocks R omega l ∧
      FKRectRefinedDualOpenWalkBlocksAlong R omega w p q l := by
  induction w generalizing p with
  | nil =>
      exact ⟨p, [], hp, FKRectSquareWalkLift.nil p hp,
        FKRectIntegralSquareDartPath.nil _,
        FKRectRefinedDualOpenEdgeBlocks.nil,
        FKRectRefinedDualOpenWalkBlocksAlong.nil p hp⟩
  | @cons x y z hxy w ih =>
      obtain ⟨d, hdopen, hedge⟩ := hxy
      let a := (fkRectLiftedIndexedEdgeEnds R d).1
      let b := (fkRectLiftedIndexedEdgeEnds R d).2
      have hcanonical := fkRectLiftedIndexedEdgeEnds_project R d
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
        have hedgePath := (fkRectRefinedDualEdgeDarts_path R d).translate t
        have hstart : fkRectRefinedDualEdgeStart R d =
            fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint a) := by
          rfl
        have hend : fkRectRefinedDualEdgeEnd R d =
            fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint b) := by
          rfl
        rw [hstart, hend,
          ← fkRectRefinedDualScale_develop_add_period R a u,
          ← fkRectRefinedDualScale_develop_add_period R b u] at hedgePath
        rw [← hu] at hedgePath
        have hdisp : q - p = fkRectDevelopedStep R x y := by
          rw [← horient.1, ← horient.2,
            fkRectLiftedIndexedEdgeEnds_developedStep R d]
          dsimp [q]
          rw [hu]
          apply Prod.ext <;> simp <;> ring
        have haxis : FKRectSquareAxisStep
            (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) := by
          rw [hu]
          dsimp [q]
          unfold FKRectSquareAxisStep
          rw [fkRectSquareDevelopPoint_sub_add_period R a b u]
          exact (fkRectLiftedIndexedEdgeEnds_squareStep R d).elim
            Or.inl (fun h => Or.inr (Or.inl h))
        have hpDeck : p =
            ((fkRectLiftedIndexedEdgeEnds R d).1.1 +
                (R.width : Int) * u.1,
              (fkRectLiftedIndexedEdgeEnds R d).1.2 +
                (R.height : Int) * u.2) := by
          simpa [a] using hu
        have hqDeck : q =
            ((fkRectLiftedIndexedEdgeEnds R d).2.1 +
                (R.width : Int) * u.1,
              (fkRectLiftedIndexedEdgeEnds R d).2.2 +
                (R.height : Int) * u.2) := by
          rfl
        let hxy' : (fkRectOpenGraph R
            (fkRectDualConfigurationEquiv R omega)).Adj x y :=
          ⟨d, hdopen, hedge⟩
        let hwhole := FKRectSquareWalkLift.cons
          (hxy := hxy') hp hq hdisp haxis hllift
        refine ⟨r, _ ++ l, hr,
          hwhole, hedgePath.append hlpath,
          FKRectRefinedDualOpenEdgeBlocks.consForward
            d u hdopen hlblocks, ?_⟩
        exact FKRectRefinedDualOpenWalkBlocksAlong.consForward
          hxy' d u hdopen hp hq hpDeck hqDeck hdisp haxis hlalong
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
          (fkRectRefinedDualEdgeDarts_path R d).reverse.translate t
        have hstart : fkRectRefinedDualEdgeStart R d =
            fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint a) := by
          rfl
        have hend : fkRectRefinedDualEdgeEnd R d =
            fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint b) := by
          rfl
        rw [hstart, hend,
          ← fkRectRefinedDualScale_develop_add_period R a u,
          ← fkRectRefinedDualScale_develop_add_period R b u] at hedgePath
        rw [← hu] at hedgePath
        have hdisp : q - p = fkRectDevelopedStep R x y := by
          rw [← horient.2, ← horient.1,
            fkRectDevelopedStep_swap,
            fkRectLiftedIndexedEdgeEnds_developedStep R d]
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
          exact (fkRectLiftedIndexedEdgeEnds_squareStep R d).elim
            Or.inl (fun h => Or.inr (Or.inl h))
        have hpDeck : p =
            ((fkRectLiftedIndexedEdgeEnds R d).2.1 +
                (R.width : Int) * u.1,
              (fkRectLiftedIndexedEdgeEnds R d).2.2 +
                (R.height : Int) * u.2) := by
          simpa [b] using hu
        have hqDeck : q =
            ((fkRectLiftedIndexedEdgeEnds R d).1.1 +
                (R.width : Int) * u.1,
              (fkRectLiftedIndexedEdgeEnds R d).1.2 +
                (R.height : Int) * u.2) := by
          rfl
        let hxy' : (fkRectOpenGraph R
            (fkRectDualConfigurationEquiv R omega)).Adj x y :=
          ⟨d, hdopen, hedge⟩
        let hwhole := FKRectSquareWalkLift.cons
          (hxy := hxy') hp hq hdisp haxis hllift
        refine ⟨r, _ ++ l, hr,
          hwhole, hedgePath.append hlpath,
          FKRectRefinedDualOpenEdgeBlocks.consReverse
            d u hdopen hlblocks, ?_⟩
        exact FKRectRefinedDualOpenWalkBlocksAlong.consReverse
          hxy' d u hdopen hp hq hpDeck hqDeck hdisp haxis hlalong



theorem exists_fkRectRefinedDualOpenWalkCarrier
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    (w : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).Walk x y)
    (p : Int × Int) (hp : fkRectLiftedVertex R p = x) :
    ∃ q : Int × Int, ∃ l : List FKRectIntegralSquareDart,
      fkRectLiftedVertex R q = y ∧
      FKRectSquareWalkLift R w p q ∧
      FKRectIntegralSquareDartPath
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q)) l ∧
      FKRectRefinedDualOpenEdgeBlocks R omega l := by
  obtain ⟨q, l, hq, hlift, hpath, hblocks, -⟩ :=
    exists_fkRectRefinedDualOpenWalkCarrierAlong R omega w p hp
  exact ⟨q, l, hq, hlift, hpath, hblocks⟩

end

end StatMech.FrontierD
