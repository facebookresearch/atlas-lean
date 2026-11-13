/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDiagonalBlockLower
import Code.FrontierD.FKRectDualSourceBarrierPattern



open Filter Topology

namespace StatMech.FrontierD

noncomputable section




theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualPullbackMulBounds
    {q : Real} (hq : 4 < q) (leftRight : Nat -> Nat)
    (hone : forall scale, 1 <= leftRight scale)
    (a : Nat -> Real) (ha : forall scale, 0 < a scale)
    (haRate : Tendsto (fun scale =>
      -Real.log (a scale) / (2 * (scale + 1) : Real)) atTop (nhds 0))
    (C : Nat -> Nat -> Real) (hC : forall scale k, 0 < C scale k)
    (hpullback : forall scale,
      ∀ᶠ k in atTop, forall blocks,
        C scale k * a scale ^ (blocks + 1) <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDualPullbackSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (leftRight scale)
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  let barrierUpper : Nat -> Real := fun scale =>
    -Real.log (a scale) / (2 * (scale + 1) : Real)
  apply fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_leftBarrierBounds
    hq leftRight hone barrierUpper
  · exact haRate
  · intro scale
    filter_upwards [hpullback scale,
      Filter.eventually_ge_atTop (leftRight scale)] with k hkpull hk
    intro delta hdelta
    exact fkRectWindingBlock_sourceBarrier_eventualUpper_of_dualPullback_mul_pow
      k scale (leftRight scale) (hone scale) (by omega)
      (by linarith : 1 <= q) (hC scale k) (ha scale) hkpull delta hdelta


theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualPullbackBounds
    {q : Real} (hq : 4 < q) (leftRight : Nat -> Nat)
    (hone : forall scale, 1 <= leftRight scale)
    (a : Nat -> Real) (ha : forall scale, 0 < a scale)
    (haRate : Tendsto (fun scale =>
      -Real.log (a scale) / (2 * (scale + 1) : Real)) atTop (nhds 0))
    (hpullback : forall scale,
      ∀ᶠ k in atTop, forall blocks,
        a scale ^ (blocks + 1) <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDualPullbackSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (leftRight scale)
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  apply fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualPullbackMulBounds
    hq leftRight hone a ha haRate (fun _ _ => 1)
    (fun _ _ => by positivity)
  intro scale
  filter_upwards [hpullback scale] with k hk
  intro blocks
  simpa using hk blocks



theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualAuxiliaryMul
    {q : Real} (hq : 4 < q) (leftRight : Nat -> Nat)
    (hone : forall scale, 1 <= leftRight scale)
    (a : Nat -> Real) (ha : forall scale, 0 < a scale)
    (haRate : Tendsto (fun scale =>
      -Real.log (a scale) / (2 * (scale + 1) : Real)) atTop (nhds 0))
    (A : forall scale k blocks,
      Set (fkRectWindingBlockVerticalFamily k scale blocks).Configuration)
    (D : Nat -> Nat -> Real) (hD : forall scale k, 0 < D scale k)
    (haux : forall scale, ∀ᶠ k in atTop, forall blocks,
      D scale k * a scale ^ (blocks + 1) <=
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (A scale k blocks))
    (hforce : forall scale, ∀ᶠ k in atTop, forall blocks,
      ∀ omega ∈ A scale k blocks,
        fkRectForceIndexedPattern
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (fkRectDualPullbackIndexSet
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (fkRectHorizontalCutEdges
                (fkRectWindingBlockVerticalFamily k scale blocks)))
            (fkRectDualPullbackConfiguration
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (fkRectAllButOneOpenConfiguration
                (fkRectWindingBlockVerticalFamily k scale blocks)
                (fkRectUnitLeftBarrierGap
                  (fkRectWindingBlockVerticalFamily k scale blocks)))) omega ∈
          fkRectDualPreimageEvent
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (fkRectNoLeftStripCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (leftRight scale))) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  let C : Nat -> Nat -> Real := fun scale k =>
    FK.cFE (fkRectCriticalP q) q ^
        (2 * (fkRectWindingBlockVerticalFamily k scale 0).width) *
      D scale k
  apply fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualPullbackMulBounds
    hq leftRight hone a ha haRate C
  · intro scale k
    dsimp [C]
    exact mul_pos
      (pow_pos (FK.cFE_pos
        (fkRectCriticalP_pos (by linarith : (0 : Real) < q))
        (fkRectCriticalP_lt_one (by linarith : (0 : Real) < q))
        (by linarith : (1 : Real) <= q)) _)
      (hD scale k)
  · intro scale
    filter_upwards [haux scale, hforce scale] with k hkaux hkforce
    intro blocks
    let R := fkRectWindingBlockVerticalFamily k scale blocks
    have hpattern :=
      fkRectCritical_cFE_pow_width_mul_auxiliary_le_dualPullbackSource
        R (leftRight scale) (by linarith : (1 : Real) <= q)
        (fkRectUnitLeftBarrierGap R) (A scale k blocks)
        (hkforce blocks)
    calc
      C scale k * a scale ^ (blocks + 1) =
          FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
            (D scale k * a scale ^ (blocks + 1)) := by
        simp [C, R]
        ring
      _ <= FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
          fkRectCriticalEventMass R q (A scale k blocks) :=
        mul_le_mul_of_nonneg_left (hkaux blocks)
          (pow_nonneg (fkRectCritical_cFE_nonneg
            (by linarith : (1 : Real) <= q)) _)
      _ <= fkRectCriticalEventMass R q
          (fkRectDualPullbackSourceLeftBarrier R (leftRight scale)
            (fkRectUnitLeftBarrierGap R)) := by
        simpa [C, R] using hpattern


theorem fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualAuxiliary
    {q : Real} (hq : 4 < q) (leftRight : Nat -> Nat)
    (hone : forall scale, 1 <= leftRight scale)
    (a : Nat -> Real) (ha : forall scale, 0 < a scale)
    (haRate : Tendsto (fun scale =>
      -Real.log (a scale) / (2 * (scale + 1) : Real)) atTop (nhds 0))
    (A : forall scale k blocks,
      Set (fkRectWindingBlockVerticalFamily k scale blocks).Configuration)
    (haux : forall scale, ∀ᶠ k in atTop, forall blocks,
      a scale ^ (blocks + 1) <=
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (A scale k blocks))
    (hforce : forall scale, ∀ᶠ k in atTop, forall blocks,
      ∀ omega ∈ A scale k blocks,
        fkRectForceIndexedPattern
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (fkRectDualPullbackIndexSet
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (fkRectHorizontalCutEdges
                (fkRectWindingBlockVerticalFamily k scale blocks)))
            (fkRectDualPullbackConfiguration
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (fkRectAllButOneOpenConfiguration
                (fkRectWindingBlockVerticalFamily k scale blocks)
                (fkRectUnitLeftBarrierGap
                  (fkRectWindingBlockVerticalFamily k scale blocks)))) omega ∈
          fkRectDualPreimageEvent
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (fkRectNoLeftStripCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (leftRight scale))) :
    fkQgt4SixVertexGapRate q <=
      fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
  apply fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualAuxiliaryMul
    hq leftRight hone a ha haRate A (fun _ _ => 1)
    (fun _ _ => by positivity)
  · intro scale
    filter_upwards [haux scale] with k hk
    intro blocks
    simpa using hk blocks
  · exact hforce

end

end StatMech.FrontierD
