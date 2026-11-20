/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRankOneWindingTail
import Code.FrontierD.FKRectAugmentedBarrierPatternCost



namespace StatMech.FrontierD

noncomputable section



theorem fkRectSource_barrierConnectionProduct_le_windingTail
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 1 ≤ q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    FK.cFE (fkRectCriticalP q) q *
        (∏ xy ∈ t,
          FK.twoPointFun
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut 1 (R.height - 1)))
            (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap) ≤
      fkRectCriticalWindingTailMass R q 1 := by
  let P := ∏ xy ∈ t,
    FK.twoPointFun
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1)))
      (fkRectCriticalP q) q xy.1 xy.2
  have hP : 0 ≤ P := by
    apply Finset.prod_nonneg
    intro xy hxy
    exact FK.twoPointFun_nonneg _
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq))
      (zero_lt_one.trans_le hq) _ _
  have hcost :=
    fkRectCritical_cFE_mul_sourceBarrier_le_augmentedSourceBarrier
      R leftRight gap x (hsep.trans_le hx) hq
  have hmul := mul_le_mul_of_nonneg_left hcost hP
  calc
    FK.cFE (fkRectCriticalP q) q * P *
          fkRectCriticalEventMass R q
            (fkRectSourceLeftBarrier R leftRight gap) =
        P * (FK.cFE (fkRectCriticalP q) q *
          fkRectCriticalEventMass R q
            (fkRectSourceLeftBarrier R leftRight gap)) := by ring
    _ ≤ P * fkRectCriticalEventMass R q
          (fkRectAugmentedSourceBarrier R leftRight gap x) := hmul
    _ ≤ fkRectCriticalWindingTailMass R q 1 :=
      fkRectAugmentedSource_barrierConnectionProduct_le_windingTail
        R leftRight cut hsep hleft hq hgap x hx hchosen t hpair

end

end StatMech.FrontierD
