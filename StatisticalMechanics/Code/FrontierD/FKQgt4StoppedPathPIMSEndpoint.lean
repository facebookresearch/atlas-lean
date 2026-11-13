/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKQgt4PIMSTwoByOnePhaseAssembly
import Code.FrontierD.FKRectHardCrossingOrientationNoGo









open Filter

namespace StatMech.FrontierD

open StatMech.FK StatMech.BeffaraDC

noncomputable section




def FKQgt4EvenTwoByOneStoppedPathPIMS (q : Real) : Prop :=
  forall scale k : Nat,
    0 < scale -> Even scale ->
    12 * scale + 2 < 2 * (k + 3) ->
    ∀ᶠ blocks in atTop,
      fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedSquareHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale) ^ 6 /
          (16 * (1 + q ^ 2)) <=
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            (fkRectWindingBlockVerticalFamily k scale blocks) scale
            0 (2 * (scale : Int)) 0 scale)



theorem fkQgt4_evenTwoByOneCrossingFloor_of_stoppedPathPIMS
    {q : Real} (hq : 1 <= q)
    (hpims : FKQgt4EvenTwoByOneStoppedPathPIMS q) :
    forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        (1 / (1 + q)) ^ 6 / (16 * (1 + q ^ 2)) <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale) := by
  intro scale k hscale hscaleEven hwidth
  filter_upwards [hpims scale k hscale hscaleEven hwidth,
    eventually_ge_atTop scale] with blocks hpimsBlock hblocks
  let R := fkRectWindingBlockVerticalFamily k scale blocks
  have hRwidth : 3 * scale < R.width := by
    dsimp only [R]
    simp only [fkRectWindingBlockVerticalFamily_width]
    omega
  have hRheight : 3 * scale < R.height := by
    dsimp only [R]
    simp only [fkRectWindingBlockVerticalFamily_height]
    nlinarith
  have hseedVertical :=
    fkRectCritical_developedSquareVerticalMass_ge_one_div_one_add_q
      R scale (by omega) hRwidth hRheight hq
  have hseedHorizontal :
      1 / (1 + q) <=
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareHorizontalCrossingEvent R scale) := by
    rw [fkRectCritical_developedSquareHorizontalMass_eq_verticalMass]
    exact hseedVertical
  apply crossing_hard_ge_of_square_seed_and_sixth_power_qsq
    hq hseedHorizontal
  simpa only [R] using hpimsBlock



theorem fkQgt4_firstOrder_of_stoppedPathPIMS
    {q : Real} (hq : 4 < q)
    (hpims : FKQgt4EvenTwoByOneStoppedPathPIMS q) :
    FK.IsFirstOrderTransition 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) := by
  let floor : Real :=
    (1 / (1 + q)) ^ 6 / (16 * (1 + q ^ 2))
  apply fkQgt4_firstOrder_of_evenTwoByOneCrossingFloor hq
    (hardFloor := floor)
  · dsimp only [floor]
    positivity
  · exact fkQgt4_evenTwoByOneCrossingFloor_of_stoppedPathPIMS
      (by linarith : (1 : Real) <= q) hpims

end

end StatMech.FrontierD
