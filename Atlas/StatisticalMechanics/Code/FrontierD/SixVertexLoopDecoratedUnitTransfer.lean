/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexLexComponentColoredSwap
import Code.FrontierD.SixVertexResolvedLoopBigradeBridge
import Code.FrontierD.SixVertexHorizontalDiagonalDeficit









namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

def sixVertexLoopDecoratedPositiveSeam
    (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt)) :
    (sixVertexPositiveSeamDisagreements T
      (sixVertexLoopDecoratedPairColored source false).arrows
      (sixVertexLoopDecoratedPairColored source true).arrows).Nonempty := by
  apply sixVertexPositiveSeamDisagreements_nonempty
    T _ _ middle.val
  · simpa [sixVertexHorizontalLowerSector] using source.1.1.2.2
  · simpa [sixVertexHorizontalUpperSector] using source.1.2.2.2
  · exact hmiddle_pos

def SixVertexLoopDecoratedLexComponentIsUnit
    (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt)) : Prop :=
  let colored := sixVertexLoopDecoratedPairColored source
  let h := sixVertexLoopDecoratedPositiveSeam
    middle hmiddle_pos hmiddle_lt source
  sixVertexTorusMaskSeamTransfer
    (sixVertexLexDisagreementComponentMask T
      (colored false).arrows (colored true).arrows h)
    (colored false).arrows (colored true).arrows = 1



def sixVertexLoopDecoratedUnitTransferTarget
    (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source) :
    SixVertexLoopDecoratedPair T middle middle := by
  let colored := sixVertexLoopDecoratedPairColored source
  let h := sixVertexLoopDecoratedPositiveSeam
    middle hmiddle_pos hmiddle_lt source
  let target := sixVertexLexDisagreementComponentColoredTarget colored h
  have htarget :=
    sixVertexLexDisagreementComponentColoredTarget_middle_of_transfer_one
      colored middle.val
      (by simpa [colored, sixVertexHorizontalLowerSector] using source.1.1.2.2)
      (by simpa [colored, sixVertexHorizontalUpperSector] using source.1.2.2.2)
      hmiddle_pos h hunit
  refine ⟨(⟨(target false).arrows,
      (target false).iceRule, htarget.1⟩,
    ⟨(target true).arrows,
      (target true).iceRule, htarget.2.1⟩),
    (target false).toCompatible, (target true).toCompatible⟩

theorem sixVertexLoopDecoratedUnitTransferTarget_colored
    (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source) :
    sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedUnitTransferTarget middle
          hmiddle_pos hmiddle_lt source hunit) =
      sixVertexLexDisagreementComponentColoredTarget
        (sixVertexLoopDecoratedPairColored source)
        (sixVertexLoopDecoratedPositiveSeam
          middle hmiddle_pos hmiddle_lt source) := by
  funext layer
  cases layer <;>
    exact FKColoredLoopPairing.toCompatible_toColored _



theorem sixVertexLoopDecoratedUnitTransferTarget_bigrade
    (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source) :
    sixVertexLoopDecoratedPairBigrade
        (sixVertexLoopDecoratedUnitTransferTarget middle
          hmiddle_pos hmiddle_lt source hunit) =
      sixVertexLoopDecoratedPairBigrade source := by
  rw [sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedUnitTransferTarget_colored]
  exact fkColoredFullSwapTarget_bigrade _ _ _

end

end StatMech.FrontierD
