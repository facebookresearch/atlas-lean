/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalBarrierCapstone





open Filter Topology

namespace StatMech.FrontierD

noncomputable section




theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossingFloor
    {q crossingFloor : Real} (hq : 4 < q)
    (hcrossingFloor : 0 < crossingFloor)
    (hcross : forall scale k : Nat,
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        crossingFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (3 * (scale : Int)) 0 scale)) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  let barrier : Nat -> Real := fun scale =>
    -Real.log
        (fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) /
      (2 * (scale + 1) : Real)
  have hfixed (scale : Nat) (hscale : 6 <= scale) :
      fkQgt4SixVertexGapRate q <=
        -Real.log
            (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) /
          (2 * (scale + 1) : Real) + barrier scale := by
    apply fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier_of_leftRight
      hq scale (4 * scale + 1) (by omega)
    filter_upwards [eventually_ge_atTop (6 * scale)] with k hk
    have hwidth : 12 * scale + 2 < 2 * (k + 3) := by omega
    exact fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossingFloor
      k scale hscale hwidth (by linarith : (1 : Real) <= q)
        hcrossingFloor (hcross scale k hwidth)
  have hdiag := (fkQgt4CriticalFreeExactDiagonalRate_tendsto hq).comp
    (tendsto_add_atTop_nat 7)
  have hdiagHalf : Tendsto (fun n : Nat =>
      -Real.log
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (n + 6 + 1)) /
        (2 * (((n + 6 : Nat) : Real) + 1))) atTop
      (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) := by
    have h := hdiag.div_const 2
    apply h.congr'
    filter_upwards with n
    simp only [Function.comp_apply]
    have hcast : ((n + 7 : Nat) : Real) =
        ((n + 6 : Nat) : Real) + 1 := by
      push_cast
      ring
    rw [hcast]
    field_simp
  have hbarrierBase :=
    fkRectDevelopedReflectedEndpointLowerOf_negLogRate_tendsto_zero
      hcrossingFloor
  have hbarrier : Tendsto (fun n : Nat => barrier (n + 6)) atTop
      (nhds 0) := by
    have hfour := (hbarrierBase.const_mul 4).comp
      (tendsto_add_atTop_nat 6)
    have heq : (fun n : Nat =>
        4 * (-Real.log
          (fkRectDevelopedReflectedEndpointLowerOf crossingFloor (n + 6)) /
          (2 * (((n + 6 : Nat) : Real) + 1)))) =ᶠ[atTop]
          (fun n => barrier (n + 6)) := by
      filter_upwards with n
      dsimp [barrier]
      rw [Real.log_pow]
      ring
    have hh := hfour.congr' (by
      simpa only [Function.comp_apply] using heq)
    simpa only [mul_zero] using hh
  have htotal := hdiagHalf.add hbarrier
  have hev : ∀ᶠ n : Nat in atTop,
      fkQgt4SixVertexGapRate q <=
        -Real.log
            (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (n + 6 + 1)) /
          (2 * (((n + 6 : Nat) : Real) + 1)) + barrier (n + 6) := by
    filter_upwards with n
    exact hfixed (n + 6) (by omega)
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds htotal hev
  simpa using hle




theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenHorizontalCrossingFloor
    {q crossingFloor : Real} (hq : 4 < q)
    (hcrossingFloor : 0 < crossingFloor)
    (hcross : forall scale k : Nat,
      Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        crossingFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (3 * (scale : Int)) 0 scale)) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  let barrier : Nat -> Real := fun scale =>
    -Real.log
        (fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) /
      (2 * (scale + 1) : Real)
  have hfixed (scale : Nat) (hscale : 6 <= scale) (hscaleEven : Even scale) :
      fkQgt4SixVertexGapRate q <=
        -Real.log
            (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) /
          (2 * (scale + 1) : Real) + barrier scale := by
    apply fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier_of_leftRight
      hq scale (4 * scale + 1) (by omega)
    filter_upwards [eventually_ge_atTop (6 * scale)] with k hk
    have hwidth : 12 * scale + 2 < 2 * (k + 3) := by omega
    exact fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossingFloor
      k scale hscale hwidth (by linarith : (1 : Real) <= q)
        hcrossingFloor (hcross scale k hscaleEven hwidth)
  have hindex : Tendsto (fun n : Nat => 2 * n + 7) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have hscaleIndex : Tendsto (fun n : Nat => 2 * n + 6) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have hdiag := (fkQgt4CriticalFreeExactDiagonalRate_tendsto hq).comp hindex
  have hdiagHalf : Tendsto (fun n : Nat =>
      -Real.log
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (2 * n + 6 + 1)) /
        (2 * (((2 * n + 6 : Nat) : Real) + 1))) atTop
      (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) := by
    have h := hdiag.div_const 2
    apply h.congr'
    filter_upwards with n
    simp only [Function.comp_apply]
    have hcast : ((2 * n + 7 : Nat) : Real) =
        ((2 * n + 6 : Nat) : Real) + 1 := by
      push_cast
      ring
    rw [hcast]
    field_simp
  have hbarrierBase :=
    fkRectDevelopedReflectedEndpointLowerOf_negLogRate_tendsto_zero
      hcrossingFloor
  have hbarrier : Tendsto (fun n : Nat => barrier (2 * n + 6)) atTop
      (nhds 0) := by
    have hfour := (hbarrierBase.const_mul 4).comp hscaleIndex
    have heq : (fun n : Nat =>
        4 * (-Real.log
          (fkRectDevelopedReflectedEndpointLowerOf crossingFloor (2 * n + 6)) /
          (2 * (((2 * n + 6 : Nat) : Real) + 1)))) =ᶠ[atTop]
          (fun n => barrier (2 * n + 6)) := by
      filter_upwards with n
      dsimp [barrier]
      rw [Real.log_pow]
      ring
    have hh := hfour.congr' (by
      simpa only [Function.comp_apply] using heq)
    simpa only [mul_zero] using hh
  have htotal := hdiagHalf.add hbarrier
  have hev : ∀ᶠ n : Nat in atTop,
      fkQgt4SixVertexGapRate q <=
        -Real.log
            (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (2 * n + 6 + 1)) /
          (2 * (((2 * n + 6 : Nat) : Real) + 1)) +
            barrier (2 * n + 6) := by
    filter_upwards with n
    apply hfixed (2 * n + 6) (by omega)
    use n + 3
    omega
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds htotal hev
  simpa using hle


theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossing
    {q : Real} (hq : 4 < q)
    (hcross : forall scale k : Nat,
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        1 / (2 * (1 + q)) <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (3 * (scale : Int)) 0 scale)) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  exact fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossingFloor
    hq (show 0 < 1 / (2 * (1 + q)) by positivity) hcross

end

end StatMech.FrontierD
