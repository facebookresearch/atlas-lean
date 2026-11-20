/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCriticalDualQuasiInvariant
import Code.FrontierD.FKRectSourceBarrierRate



open Filter Topology

namespace StatMech.FrontierD

noncomputable section



def fkRectDualPullbackSourceLeftBarrier (R : FKRectTorus)
    (leftRight : Nat) (gap : R.EdgeIndex) : Set R.Configuration :=
  fkRectDualPreimageEvent R (fkRectSourceLeftBarrier R leftRight gap)

theorem fkRectDualEvent_pullbackSourceLeftBarrier
    (R : FKRectTorus) (leftRight : Nat) (gap : R.EdgeIndex) :
    fkRectDualEvent R
        (fkRectDualPullbackSourceLeftBarrier R leftRight gap) =
      fkRectSourceLeftBarrier R leftRight gap := by
  exact fkRectDualEvent_dualPreimageEvent R _



theorem one_div_q_mul_dualPullbackSourceMass_le_sourceBarrier
    (R : FKRectTorus) (leftRight : Nat) {q : Real} (hq : 1 <= q)
    (gap : R.EdgeIndex) :
    (1 / q) * fkRectCriticalEventMass R q
        (fkRectDualPullbackSourceLeftBarrier R leftRight gap) <=
      fkRectCriticalEventMass R q
        (fkRectSourceLeftBarrier R leftRight gap) := by
  apply one_div_q_mul_eventMass_le_of_dualEvent_subset R hq
  rw [fkRectDualEvent_pullbackSourceLeftBarrier]



theorem fkRectSourceBarrier_negLogRate_le_of_dualPullback_mul_pow
    (R : FKRectTorus) (leftRight blocks : Nat)
    (hone : 1 <= leftRight) (hleft : leftRight + 1 < R.width)
    {q C a : Real} (hq : 1 <= q) (hC : 0 < C) (ha : 0 < a)
    (haux : C * a ^ blocks <= fkRectCriticalEventMass R q
      (fkRectDualPullbackSourceLeftBarrier R leftRight
        (fkRectUnitLeftBarrierGap R))) :
    -Real.log (fkRectCriticalEventMass R q
        (fkRectSourceLeftBarrier R leftRight
          (fkRectUnitLeftBarrierGap R))) / R.height <=
      (blocks : Real) * (-Real.log a) / R.height +
        (-Real.log ((1 / q) * C)) / R.height := by
  let c : Real := (1 / q) * C
  let B := fkRectCriticalEventMass R q
    (fkRectSourceLeftBarrier R leftRight (fkRectUnitLeftBarrierGap R))
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (by positivity) hC
  have hB : 0 < B := by
    dsimp [B]
    exact fkRectCriticalEventMass_pos_of_mem R (by linarith) _
      (fkRectUnitLeftBarrierConfiguration R)
      (fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le
        R leftRight hone hleft)
  have htransfer :=
    one_div_q_mul_dualPullbackSourceMass_le_sourceBarrier
      R leftRight hq (fkRectUnitLeftBarrierGap R)
  have hlower : c * a ^ blocks <= B := by
    calc
      c * a ^ blocks = (1 / q) * (C * a ^ blocks) := by
        dsimp [c]
        ring
      _ <= (1 / q) * fkRectCriticalEventMass R q
          (fkRectDualPullbackSourceLeftBarrier R leftRight
            (fkRectUnitLeftBarrierGap R)) :=
        mul_le_mul_of_nonneg_left haux (by positivity)
      _ <= B := by simpa [c, B] using htransfer
  have hlog := Real.log_le_log
    (mul_pos hc (pow_pos ha _)) hlower
  rw [Real.log_mul hc.ne' (pow_pos ha _).ne', Real.log_pow] at hlog
  have hnum : -Real.log B <=
      (blocks : Real) * (-Real.log a) + (-Real.log c) := by
    linarith
  calc
    -Real.log B / R.height <=
        ((blocks : Real) * (-Real.log a) + (-Real.log c)) / R.height :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (blocks : Real) * (-Real.log a) / R.height +
        (-Real.log c) / R.height := by ring
    _ = _ := by rfl


theorem fkRectSourceBarrier_negLogRate_le_of_dualPullbackPow
    (R : FKRectTorus) (leftRight blocks : Nat)
    (hone : 1 <= leftRight) (hleft : leftRight + 1 < R.width)
    {q a : Real} (hq : 1 <= q) (ha : 0 < a)
    (haux : a ^ blocks <= fkRectCriticalEventMass R q
      (fkRectDualPullbackSourceLeftBarrier R leftRight
        (fkRectUnitLeftBarrierGap R))) :
    -Real.log (fkRectCriticalEventMass R q
        (fkRectSourceLeftBarrier R leftRight
          (fkRectUnitLeftBarrierGap R))) / R.height <=
      (blocks : Real) * (-Real.log a) / R.height +
        (-Real.log (1 / q)) / R.height := by
  simpa using
    (fkRectSourceBarrier_negLogRate_le_of_dualPullback_mul_pow
      R leftRight blocks hone hleft hq (by positivity : (0 : Real) < 1)
      ha (by simpa using haux))



theorem fkRectWindingBlock_sourceBarrier_eventualUpper_of_dualPullback_mul_pow
    (k scale leftRight : Nat) (hone : 1 <= leftRight)
    (hleft : leftRight + 1 < 2 * (k + 3))
    {q C a : Real} (hq : 1 <= q) (hC : 0 < C) (ha : 0 < a)
    (haux : forall blocks,
      C * a ^ (blocks + 1) <=
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDualPullbackSourceLeftBarrier
            (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
            (fkRectUnitLeftBarrierGap
              (fkRectWindingBlockVerticalFamily k scale blocks)))) :
    forall epsilon : Real, 0 < epsilon -> ∀ᶠ blocks in atTop,
      -Real.log
          (fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
        -Real.log a / (2 * (scale + 1) : Real) + epsilon := by
  intro epsilon hepsilon
  let blockCost : Nat -> Real := fun blocks =>
    ((blocks + 1 : Nat) : Real) * (-Real.log a) /
      (fkRectWindingBlockVerticalFamily k scale blocks).height
  let dualConstant : Real := -Real.log ((1 / q) * C)
  let dualCost : Nat -> Real := fun blocks =>
    dualConstant /
      (fkRectWindingBlockVerticalFamily k scale blocks).height
  have hblock : Tendsto blockCost atTop
      (nhds (-Real.log a / (2 * (scale + 1) : Real))) := by
    have h := (fkRectWindingBlock_count_div_height_tendsto k scale).mul_const
      (-Real.log a)
    convert h using 1
    · funext blocks
      simp only [blockCost, fkRectWindingBlockVerticalFamily_height,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    · ring
  have hheightNat := tendsto_fkRectWindingBlockVerticalFamily_height k scale
  have hheight : Tendsto (fun blocks =>
      ((fkRectWindingBlockVerticalFamily k scale blocks).height : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hheightNat
  have hdual : Tendsto dualCost atTop (nhds 0) :=
    hheight.const_div_atTop dualConstant
  have hevent : ∀ᶠ blocks in atTop,
      blockCost blocks + dualCost blocks <
        -Real.log a / (2 * (scale + 1) : Real) + epsilon :=
    (tendsto_order.1 (hblock.add hdual)).2 _ (by linarith)
  filter_upwards [hevent] with blocks hcost
  have hfinite := fkRectSourceBarrier_negLogRate_le_of_dualPullback_mul_pow
    (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (blocks + 1)
    hone hleft hq hC ha (haux blocks)
  change -Real.log
          (fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) /
        (fkRectWindingBlockVerticalFamily k scale blocks).height <=
      -Real.log a / (2 * (scale + 1) : Real) + epsilon
  dsimp [blockCost, dualCost, dualConstant] at hcost
  exact hfinite.trans hcost.le


theorem fkRectWindingBlock_sourceBarrier_eventualUpper_of_dualPullback
    (k scale leftRight : Nat) (hone : 1 <= leftRight)
    (hleft : leftRight + 1 < 2 * (k + 3))
    {q a : Real} (hq : 1 <= q) (ha : 0 < a)
    (haux : forall blocks,
      a ^ (blocks + 1) <=
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDualPullbackSourceLeftBarrier
            (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
            (fkRectUnitLeftBarrierGap
              (fkRectWindingBlockVerticalFamily k scale blocks)))) :
    forall epsilon : Real, 0 < epsilon -> ∀ᶠ blocks in atTop,
      -Real.log
          (fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height <=
        -Real.log a / (2 * (scale + 1) : Real) + epsilon := by
  apply fkRectWindingBlock_sourceBarrier_eventualUpper_of_dualPullback_mul_pow
    k scale leftRight hone hleft hq (by positivity : (0 : Real) < 1) ha
  intro blocks
  simpa using haux blocks

end

end StatMech.FrontierD
