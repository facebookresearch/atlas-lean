/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectVerticalWindingCutFiberBalance
import Code.FrontierD.FKRectHorizontalCylinderTransverseTail









namespace StatMech.FrontierD

noncomputable section



def FKRectRankOnePositiveVerticalBoundaryCutFiberBound
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ K : (fkRectOpenGraph R omega).ConnectedComponent,
    ¬ FKRectPrimalComponentHasNet R omega K →
      fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤
        fkRectPrimalComponentHorizontalCutCrossingCount R omega K



theorem fkRectPositiveVerticalBoundaryCutFiberBound_of_rankOne
    (R : FKRectTorus) (omega : R.Configuration)
    (h : FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega) :
    FKRectPositiveVerticalBoundaryCutFiberBound R omega := by
  intro K
  by_cases hnet : FKRectPrimalComponentHasNet R omega K
  · exact fkRectPositiveVerticalBoundaryCutFiberBound_of_componentHasNet
      R omega K hnet
  · exact h K hnet



theorem fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_rankOne
    (R : FKRectTorus) (omega : R.Configuration)
    (h : FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega) :
    fkRectUnorientedVerticalWindingNumber R omega ≤
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) :=
  fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_positiveFiberBound
    R omega
      (fkRectPositiveVerticalBoundaryCutFiberBound_of_rankOne R omega h)



theorem fkRectWindingTailForcesHorizontalCylinderCrossings_of_rankOne
    (R : FKRectTorus) (r : Nat)
    (h : ∀ omega, FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega) :
    FKRectWindingTailForcesHorizontalCylinderCrossings R r := by
  intro omega homega
  exact homega.trans
    (fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_rankOne
      R omega (h omega))

end

end StatMech.FrontierD
