/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonPrimitive
import Code.FrontierD.FKRectBoundaryIncidenceConnected
import Code.FrontierD.FKRectVerticalWindingUnitInjection



namespace StatMech.FrontierD



theorem rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two_unconditional
    (R : FKRectTorus) (omega : R.Configuration)
    (hcard : ∀ K : (fkRectOpenGraph R omega).ConnectedComponent,
      ¬ FKRectPrimalComponentHasNet R omega K →
        (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2) :
    FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega := by
  apply rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two
    R omega hcard
  intro d hpos
  exact fkRectBlackBoundaryPrimalCycleWinding_primitive_of_snd_pos
    R omega d hpos



theorem fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_card_nonzero_le_two
    (R : FKRectTorus) (omega : R.Configuration)
    (hcard : ∀ K : (fkRectOpenGraph R omega).ConnectedComponent,
      ¬ FKRectPrimalComponentHasNet R omega K →
        (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2) :
    fkRectUnorientedVerticalWindingNumber R omega ≤
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) := by
  apply fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_rankOne
  exact rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two_unconditional
    R omega hcard



theorem fkRectWindingTailForcesHorizontalCylinderCrossings_of_card_nonzero_le_two
    (R : FKRectTorus) (r : Nat)
    (hcard : ∀ omega K,
      ¬ FKRectPrimalComponentHasNet R omega K →
        (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2) :
    FKRectWindingTailForcesHorizontalCylinderCrossings R r := by
  apply fkRectWindingTailForcesHorizontalCylinderCrossings_of_rankOne
  intro omega
  exact rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two_unconditional
    R omega (hcard omega)



theorem rankOnePositiveBoundaryCutFiberBound_unconditional
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega := by
  apply rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two_unconditional
  intro K _
  exact card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two R omega K



theorem fkRectUnorientedVerticalWindingNumber_le_horizontalCut
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectUnorientedVerticalWindingNumber R omega ≤
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) := by
  apply fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_card_nonzero_le_two
  intro K _
  exact card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two R omega K



theorem fkRectWindingTailForcesHorizontalCylinderCrossings_unconditional
    (R : FKRectTorus) (r : Nat) :
    FKRectWindingTailForcesHorizontalCylinderCrossings R r := by
  apply fkRectWindingTailForcesHorizontalCylinderCrossings_of_card_nonzero_le_two
  intro omega K _
  exact card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two R omega K

end StatMech.FrontierD
