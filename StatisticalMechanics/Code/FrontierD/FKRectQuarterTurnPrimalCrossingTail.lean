/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectPrimalAdaptiveProjection
import Code.FrontierD.FKRectQuarterTurn











namespace StatMech.FrontierD

noncomputable section




theorem fkRectQuarterTurnCriticalCutFree_primalCrossingTail_le_choose_mul_pow
    (R : FKRectTorus) (hheight : 4 < R.height)
    {q : Real} (hq : 1 <= q) (n : Nat) :
    fkRectCriticalCutFreeEventMass (fkRectQuarterTurnTorus R hheight) q
        {eta | n < fkRectRawHorizontalCrossingClusterCount
          (fkRectQuarterTurnTorus R hheight)
          (fkRectForceCutClosed (fkRectQuarterTurnTorus R hheight) eta)} <=
      Nat.choose (2 * R.width) (n + 1) *
        ((StatMech.FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure
              (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real
          (StatMech.FK.boxBdryConnEvent 2 (R.height / 2 - 2))) ^ (n + 1) := by
  simpa only [fkRectQuarterTurnTorus_width, fkRectQuarterTurnTorus_height]
    using fkRectCriticalCutFree_primalCrossingTail_le_choose_mul_pow
      (fkRectQuarterTurnTorus R hheight) hq n

end

end StatMech.FrontierD
