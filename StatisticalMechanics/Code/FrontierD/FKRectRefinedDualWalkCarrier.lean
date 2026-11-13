/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedDualOpenWalkCarrier
import Code.FrontierD.FKRectRefinedWalkCarrier



namespace StatMech.FrontierD

noncomputable section



structure FKRectRefinedDualWalkCarrier
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) where
  darts : List FKRectIntegralSquareDart
  path : FKRectIntegralSquareDartPath
    (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))
    (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q)) darts




def FKRectRefinedDualWalkCarrier.translation
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (_D : FKRectRefinedDualWalkCarrier R h) : Int × Int :=
  (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
    4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)



theorem FKRectRefinedDualWalkCarrier.path_translation
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (D : FKRectRefinedDualWalkCarrier R h) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))
      ((fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).1 +
          D.translation.1,
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).2 +
          D.translation.2)
      D.darts := by
  have hend : fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q) =
      ((fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).1 +
          D.translation.1,
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).2 +
          D.translation.2) := by
    apply Prod.ext <;>
      simp [FKRectRefinedDualWalkCarrier.translation,
        fkRectRefinedDualScalePoint] <;> ring
  rw [← hend]
  exact D.path



def FKRectRefinedDualWalkCarrier.coverDarts
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (D : FKRectRefinedDualWalkCarrier R h) :=
  fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
    D.darts D.translation




theorem FKRectRefinedDualWalkCarrier.interaction_ne_zero_iff_windingIndependent
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {z : G.Walk x x} {w : H.Walk y y}
    {p q a b : Int × Int}
    {hz : FKRectSquareWalkLift R z p q}
    {hw : FKRectSquareWalkLift R w a b}
    (D : FKRectRefinedDualWalkCarrier R hz)
    (C : FKRectRefinedWalkCarrier R hw) :
    fkRectRefinedRawInteraction D.coverDarts C.coverDarts ≠ 0 ↔
      FKRectWindingIndependent
        (fkRectWalkWinding R z) (fkRectWalkWinding R w) := by
  change fkRectRefinedRawInteraction
      (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
        D.darts D.translation)
      (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
        C.darts C.translation) ≠ 0 ↔ _
  rw [fkRectSquareCoverDartList_interaction_ne_zero_iff
    (fkRectRefinedCoverTorus R) D.path_translation C.path_translation]
  change FKRectWindingIndependent
      (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)
      (4 * (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a).1,
        4 * (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a).2) ↔ _
  rw [fkRectWindingIndependent_four_iff]
  exact hz.closed_developedIndependent_iff R hw

end

end StatMech.FrontierD
