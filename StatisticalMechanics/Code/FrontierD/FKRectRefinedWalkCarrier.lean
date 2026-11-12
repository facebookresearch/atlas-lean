/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedIntersection
import Code.FrontierD.FKRectSquareCoverDartList









namespace StatMech.FrontierD

noncomputable section



structure FKRectRefinedWalkCarrier
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) where
  darts : List FKRectIntegralSquareDart
  path : FKRectIntegralSquareDartPath
    (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))
    (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) darts


theorem FKRectSquareWalkLift.exists_refinedWalkCarrier
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    Nonempty (FKRectRefinedWalkCarrier R h) := by
  obtain ⟨darts, hdarts⟩ := h.exists_refinedDartPath R
  exact ⟨⟨darts, hdarts⟩⟩


def FKRectRefinedWalkCarrier.translation
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (_C : FKRectRefinedWalkCarrier R h) : Int × Int :=
  (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
    4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)


theorem FKRectRefinedWalkCarrier.path_translation
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (C : FKRectRefinedWalkCarrier R h) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))
      ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 +
          C.translation.1,
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 +
          C.translation.2)
      C.darts := by
  have hend : fkRectRefinedScalePoint (fkRectSquareDevelopPoint q) =
      ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 +
          C.translation.1,
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 +
          C.translation.2) := by
    apply Prod.ext <;>
      simp [FKRectRefinedWalkCarrier.translation,
        fkRectRefinedScalePoint] <;> ring
  rw [← hend]
  exact C.path


def FKRectRefinedWalkCarrier.coverDarts
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (C : FKRectRefinedWalkCarrier R h) :=
  fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
    C.darts C.translation



theorem FKRectRefinedWalkCarrier.interaction_ne_zero_iff_windingIndependent
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x x} {z : H.Walk y y}
    {p q a b : Int × Int}
    {hw : FKRectSquareWalkLift R w p q}
    {hz : FKRectSquareWalkLift R z a b}
    (C : FKRectRefinedWalkCarrier R hw)
    (D : FKRectRefinedWalkCarrier R hz) :
    fkRectRefinedRawInteraction C.coverDarts D.coverDarts ≠ 0 ↔
      FKRectWindingIndependent
        (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  change fkRectRefinedRawInteraction
      (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
        C.darts C.translation)
      (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
        D.darts D.translation) ≠ 0 ↔ _
  rw [fkRectSquareCoverDartList_interaction_ne_zero_iff
    (fkRectRefinedCoverTorus R) C.path_translation D.path_translation]
  change FKRectWindingIndependent
      (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)
      (4 * (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a).1,
        4 * (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a).2) ↔ _
  rw [fkRectWindingIndependent_four_iff]
  exact hw.closed_developedIndependent_iff R hz

end

end StatMech.FrontierD
