/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectPrimalBoundaryCompanionUnique
import Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight









namespace StatMech.FrontierD

noncomputable section




def FKRectPrimalRankOneRegularNeighborhood.ofCompanionUnique
    (R : FKRectTorus) (omega : R.Configuration)
    (hunique : ¬ FKRectHasNet R omega ->
      FKRectPrimalBoundaryCompanionUnique R omega)
    (hextreme : FKRectPrimalDevelopedExtremeSameSign R omega) :
    FKRectPrimalRankOneRegularNeighborhood R omega :=
  FKRectPrimalRankOneRegularNeighborhood.ofParts R omega
    (fkRectPrimalBoundaryFiberSameSignUnique_of_card_nonzero_le_two
      R omega (fun hnoNet x =>
        card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_companionUnique
          R omega (hunique hnoNet) x))
    hextreme



theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_companionUnique_height
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (hunique : forall omega : R.Configuration,
      ¬ FKRectHasNet R omega ->
        FKRectPrimalBoundaryCompanionUnique R omega)
    (hextreme : forall omega : R.Configuration,
      FKRectPrimalDevelopedExtremeSameSign R omega)
    (hdual : forall omega : R.Configuration,
      FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) <=
      fkRectAllSectorNormalization R q := by
  apply zeroTurnCost_div_two_q_le_allSectorNormalization_of_regularNeighborhood_height
    R hq
  · intro omega
    exact FKRectPrimalRankOneRegularNeighborhood.ofCompanionUnique
      R omega (hunique omega) (hextreme omega)
  · exact hdual

end

end StatMech.FrontierD
