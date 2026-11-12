/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectAugmentedBarrierWindingMass
import Code.FrontierD.FKRectLeftStripNoNet



namespace StatMech.FrontierD

noncomputable section




def fkRectVerticalRankOneEvent (R : FKRectTorus) : Set R.Configuration :=
  fkRectVerticalWindingEvent R ∩ {omega | ¬ FKRectHasNet R omega}



theorem fkRectSeparatedVerticalWindingEvent_subset_verticalRankOne
    (R : FKRectTorus) (leftRight : Nat)
    (hleft : leftRight + 1 < R.width) :
    fkRectSeparatedVerticalWindingEvent R leftRight ⊆
      fkRectVerticalRankOneEvent R := by
  rintro omega ⟨hno, hvertical⟩
  exact ⟨hvertical,
    not_fkRectHasNet_of_noLeftStripCrossing
      R omega leftRight hleft hno⟩



theorem fkRectCriticalSeparatedVerticalWindingMass_le_verticalRankOneMass
    (R : FKRectTorus) (leftRight : Nat)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 0 < q) :
    fkRectCriticalEventMass R q
        (fkRectSeparatedVerticalWindingEvent R leftRight) ≤
      fkRectCriticalEventMass R q (fkRectVerticalRankOneEvent R) :=
  fkRectCriticalEventMass_mono R hq
    (fkRectSeparatedVerticalWindingEvent_subset_verticalRankOne
      R leftRight hleft)



theorem fkRectAugmentedSource_barrierConnectionProduct_le_verticalRankOneMass
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
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectAugmentedSourceBarrier R leftRight gap x) ≤
      fkRectCriticalEventMass R q (fkRectVerticalRankOneEvent R) := by
  exact (fkRectAugmentedSource_barrierConnectionProduct_le_separatedWindingMass
    R leftRight cut hsep hq hgap x hx hchosen t hpair).trans
      (fkRectCriticalSeparatedVerticalWindingMass_le_verticalRankOneMass
        R leftRight hleft (zero_lt_one.trans_le hq))

end

end StatMech.FrontierD
