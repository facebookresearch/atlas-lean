/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedDistinctEdgeSupport
import Code.FrontierD.FKRectRefinedRepeatedInteraction









namespace StatMech.FrontierD

noncomputable section



theorem fkRectRefinedLocalDarts_add_center
    (pairing : Bool) (c t : Int × Int) (side : FKMedialSide) :
    fkRectRefinedLocalDarts pairing (c.1 + t.1, c.2 + t.2) side =
      (fkRectRefinedLocalDarts pairing c side).map
        (fkRectIntegralSquareDartTranslate t) := by
  cases pairing <;> cases side <;>
    simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
      fkRectRefinedSideOffset, fkRectIntegralSquareDartTranslate]
  all_goals repeat' constructor
  all_goals ring



theorem fkRectRefinedPrimalCenterlineDarts_add_center
    (pairing : Bool) (c t : Int × Int) :
    fkRectRefinedPrimalCenterlineDarts pairing
        (c.1 + t.1, c.2 + t.2) =
      (fkRectRefinedPrimalCenterlineDarts pairing c).map
        (fkRectIntegralSquareDartTranslate t) := by
  cases pairing <;>
    simp [fkRectRefinedPrimalCenterlineDarts,
      fkRectIntegralSquareDartTranslate]
  all_goals repeat' constructor
  all_goals ring



theorem fkRectRefinedLocalDarts_west_interaction_add_center
    (R : FKRectTorus) (pairing : Bool) (c t : Int × Int) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts pairing
            (c.1 + t.1, c.2 + t.2) .west).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))))
        ((fkRectRefinedPrimalCenterlineDarts pairing
            (c.1 + t.1, c.2 + t.2)).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = 1 := by
  rw [fkRectRefinedLocalDarts_add_center,
    fkRectRefinedPrimalCenterlineDarts_add_center]
  simpa only [List.map_map] using
    (fkRectRefinedRawInteraction_integralTranslate
      (L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)) t
      (fkRectRefinedLocalDarts pairing c .west)
      (fkRectRefinedPrimalCenterlineDarts pairing c)).trans
        (fkRectRefinedLocalDarts_west_interaction pairing c)



theorem fkRectRefinedLocalDarts_east_interaction_add_center
    (R : FKRectTorus) (pairing : Bool) (c t : Int × Int) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts pairing
            (c.1 + t.1, c.2 + t.2) .east).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))))
        ((fkRectRefinedPrimalCenterlineDarts pairing
            (c.1 + t.1, c.2 + t.2)).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = -1 := by
  rw [fkRectRefinedLocalDarts_add_center,
    fkRectRefinedPrimalCenterlineDarts_add_center]
  simpa only [List.map_map] using
    (fkRectRefinedRawInteraction_integralTranslate
      (L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)) t
      (fkRectRefinedLocalDarts pairing c .east)
      (fkRectRefinedPrimalCenterlineDarts pairing c)).trans
        (fkRectRefinedLocalDarts_east_interaction pairing c)

end

end StatMech.FrontierD
