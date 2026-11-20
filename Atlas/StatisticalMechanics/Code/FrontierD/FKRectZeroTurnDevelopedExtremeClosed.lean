/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnDevelopedAnchor









namespace StatMech.FrontierD

noncomputable section



theorem fkRectRawPrimalCrossingDevelopedExtremeDart_edge_closed
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) :
    omega (fkRectTorusMedialEdgeEquiv R
      (fkRectRawPrimalCrossingDevelopedExtremeDart
        R omega X side).1) = false := by
  cases side
  · by_cases hbottom : Even
        (fkRectRawPrimalCrossingBottomVertex R omega X).2.val <;>
      simpa [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectMedialDartAtPrimalVertex, fkMedialWestDart,
        fkMedialEastDart, hbottom] using
          fkRectRawPrimalCrossingBottomEdge_closed R omega C X
  · by_cases htop : Even
        (finitePeriodicSucc R.height_pos
          (fkRectRawPrimalCrossingTopVertex R omega X).2).val <;>
      simpa [fkRectRawPrimalCrossingDevelopedExtremeDart,
        fkRectMedialDartAbovePrimalVertex, fkMedialWestDart,
        fkMedialEastDart, htop] using
          fkRectRawPrimalCrossingTopEdge_closed R omega C X

end

end StatMech.FrontierD
