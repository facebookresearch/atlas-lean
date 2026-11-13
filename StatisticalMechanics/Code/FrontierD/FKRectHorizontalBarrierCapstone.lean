/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedHorizontalEndpoint
import Code.FrontierD.FKRectPositiveBandBlockRepetition
import Code.FrontierD.FKRectDiagonalBlockLower



open Set SimpleGraph Filter Topology

namespace StatMech.FrontierD

noncomputable section




def fkRectPositiveBandBarrierConstant
    (k scale : Nat) (q : Real) : Real :=
  let c := FK.cFE (fkRectCriticalP q) q
  c ^ (2 * (2 * (k + 3))) *
    (((c ^ ((4 * scale + 1) * (24 * scale + 4))) *
      c ^ ((4 * scale + 1) * (40 * scale + 7))) * c)

theorem fkRectPositiveBandBarrierConstant_pos
    (k scale : Nat) {q : Real} (hq : 1 ≤ q) :
    0 < fkRectPositiveBandBarrierConstant k scale q := by
  unfold fkRectPositiveBandBarrierConstant
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq
  positivity



theorem fkRectPositiveBandBulkBlocks_le_four_mul
    {k scale blocks : Nat} {q : Real}
    (hscale : 6 ≤ scale)
    (B : FKRectPositiveBandOrientedBlock
      (fkRectWindingBlockVerticalFamily k scale blocks) q scale) :
    fkRectPositiveBandBulkBlocks B ≤ 4 * (blocks + 1) := by
  apply Nat.div_le_of_le_mul
  have hstep : scale - 2 ≤ B.step := by
    have := B.step_scale
    omega
  have hheight :
      (fkRectWindingBlockVerticalFamily k scale blocks).height ≤
        4 * (blocks + 1) * (scale - 2) := by
    simp only [fkRectWindingBlockVerticalFamily_height]
    calc
      2 * (scale + 1) * (blocks + 1) + 2 ≤
          (2 * (scale + 1) + 2) * (blocks + 1) := by
        ring_nf
        exact Nat.add_le_add_left (by omega) _
      _ ≤ (4 * (scale - 2)) * (blocks + 1) :=
        Nat.mul_le_mul_right (blocks + 1) (by omega)
      _ = 4 * (blocks + 1) * (scale - 2) := by ring
  calc
    (fkRectWindingBlockVerticalFamily k scale blocks).height - 1 -
          (24 * scale + 4) ≤
        (fkRectWindingBlockVerticalFamily k scale blocks).height := by omega
    _ ≤ 4 * (blocks + 1) * (scale - 2) := hheight
    _ ≤ B.step * (4 * (blocks + 1)) := by
      rw [mul_comm B.step, mul_assoc]
      simpa [mul_assoc] using
        (Nat.mul_le_mul_left (4 * (blocks + 1)) hstep)

theorem FKRectPositiveBandOrientedBlock.massFloor_le_one
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (hq : 1 ≤ q) (B : FKRectPositiveBandOrientedBlock R q scale) :
    B.massFloor ≤ 1 := by
  have hmass : fkRectCriticalEventMass R q
      {omega | FKRectConnectedWithin R omega B.carrier B.start B.finish} ≤
      fkRectCriticalEventMass R q Set.univ :=
    fkRectCriticalEventMass_mono R (zero_lt_one.trans_le hq)
      (Set.subset_univ _)
  rw [fkRectCriticalEventMass_univ R (zero_lt_one.trans_le hq)] at hmass
  exact B.mass_lower.trans hmass

theorem fkRectDevelopedReflectedEndpointLower_le_one
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (hq : 1 ≤ q) (B : FKRectPositiveBandOrientedBlock R q scale)
    (hB : B.massFloor = fkRectDevelopedReflectedEndpointLower q scale) :
    fkRectDevelopedReflectedEndpointLower q scale ≤ 1 := by
  rw [← hB]
  exact B.massFloor_le_one hq




theorem fkRectWindingBlock_eventually_dualPullbackLower_of_horizontalCrossingFloor
    (k scale : Nat) (hscale : 6 ≤ scale)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    {q crossingFloor : Real} (hq : 1 ≤ q)
    (hcrossingFloor : 0 < crossingFloor)
    (hcross : ∀ᶠ blocks in atTop,
      crossingFloor ≤
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            (fkRectWindingBlockVerticalFamily k scale blocks) scale
            0 (3 * (scale : Int)) 0 scale)) :
    ∀ᶠ blocks in atTop,
      fkRectPositiveBandBarrierConstant k scale q *
          (fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) ^
            (blocks + 1) ≤
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDualPullbackSourceLeftBarrier
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (4 * scale + 1)
            (fkRectUnitLeftBarrierGap
              (fkRectWindingBlockVerticalFamily k scale blocks))) := by
  filter_upwards [hcross, eventually_ge_atTop (40 * scale + 8)] with
    blocks hcrossBlock hblocks
  let R := fkRectWindingBlockVerticalFamily k scale blocks
  have hRwidth : 12 * scale + 2 < R.width := by
    simpa [R] using hwidth
  have hRtall : 40 * scale + 6 < R.height - 1 := by
    dsimp [R]
    nlinarith
  have hRheight : 12 * scale + 2 < R.height := by omega
  obtain ⟨B, hB⟩ :=
    fkRectCritical_developedThreeByOne_exists_horizontalPositiveBandBlock_of_crossingFloor
      R scale (by omega) hRwidth hRheight hq hcrossingFloor
        (by simpa [R] using hcrossBlock)
  have hbandHeight : 24 * scale + 4 ≤ R.height - 1 := by omega
  have hlower := fkRectCritical_concretePositiveBandDualBarrierLower
    B hbandHeight (by omega) hRtall (by omega) hq
  rw [hB] at hlower
  have ha0 : 0 ≤
      fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale :=
    (fkRectDevelopedReflectedEndpointLowerOf_pos
      hcrossingFloor scale).le
  have ha1 : fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ≤ 1 := by
    rw [← hB]
    exact B.massFloor_le_one hq
  have hbulk := fkRectPositiveBandBulkBlocks_le_four_mul hscale B
  have hpow :
      (fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) ^
          (blocks + 1) ≤
        fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^
          fkRectPositiveBandBulkBlocks B := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one ha0 ha1 (by omega)
  have hc0 : 0 ≤ FK.cFE (fkRectCriticalP q) q :=
    (FK.cFE_pos (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq).le
  have hlower' :
      FK.cFE (fkRectCriticalP q) q ^ (2 * (2 * (k + 3))) *
        (((fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^
              fkRectPositiveBandBulkBlocks B *
            FK.cFE (fkRectCriticalP q) q ^
              ((4 * scale + 1) * (24 * scale + 4))) *
          FK.cFE (fkRectCriticalP q) q ^
            ((4 * scale + 1) * (40 * scale + 7))) *
          FK.cFE (fkRectCriticalP q) q) ≤
        fkRectCriticalEventMass R q
          (fkRectDualPullbackSourceLeftBarrier R (4 * scale + 1)
            (fkRectUnitLeftBarrierGap R)) := by
    simpa [R, fkRectWindingBlockVerticalFamily_width] using hlower
  unfold fkRectPositiveBandBarrierConstant
  dsimp only
  apply le_trans ?_ hlower'
  rw [show
    FK.cFE (fkRectCriticalP q) q ^ (2 * (2 * (k + 3))) *
          (FK.cFE (fkRectCriticalP q) q ^
              ((4 * scale + 1) * (24 * scale + 4)) *
            FK.cFE (fkRectCriticalP q) q ^
              ((4 * scale + 1) * (40 * scale + 7)) *
            FK.cFE (fkRectCriticalP q) q) *
        (fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) ^
          (blocks + 1) =
      FK.cFE (fkRectCriticalP q) q ^ (2 * (2 * (k + 3))) *
        ((FK.cFE (fkRectCriticalP q) q ^
              ((4 * scale + 1) * (24 * scale + 4)) *
            FK.cFE (fkRectCriticalP q) q ^
              ((4 * scale + 1) * (40 * scale + 7)) *
            FK.cFE (fkRectCriticalP q) q) *
          (fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) ^
            (blocks + 1)) by ring]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc0 _)
  calc
    (((FK.cFE (fkRectCriticalP q) q ^
            ((4 * scale + 1) * (24 * scale + 4)) *
          FK.cFE (fkRectCriticalP q) q ^
            ((4 * scale + 1) * (40 * scale + 7))) *
        FK.cFE (fkRectCriticalP q) q) *
          (fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) ^
            (blocks + 1) =
      (((fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) ^
            (blocks + 1) *
          FK.cFE (fkRectCriticalP q) q ^
            ((4 * scale + 1) * (24 * scale + 4))) *
        FK.cFE (fkRectCriticalP q) q ^
          ((4 * scale + 1) * (40 * scale + 7))) *
        FK.cFE (fkRectCriticalP q) q) := by ring
    _ ≤ (((fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^
            fkRectPositiveBandBulkBlocks B *
          FK.cFE (fkRectCriticalP q) q ^
            ((4 * scale + 1) * (24 * scale + 4))) *
        FK.cFE (fkRectCriticalP q) q ^
          ((4 * scale + 1) * (40 * scale + 7))) *
        FK.cFE (fkRectCriticalP q) q) := by
      apply mul_le_mul_of_nonneg_right _ hc0
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hc0 _)
      exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hc0 _)



theorem fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossingFloor
    (k scale : Nat) (hscale : 6 ≤ scale)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    {q crossingFloor : Real} (hq : 1 ≤ q)
    (hcrossingFloor : 0 < crossingFloor)
    (hcross : ∀ᶠ blocks in atTop,
      crossingFloor ≤
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            (fkRectWindingBlockVerticalFamily k scale blocks) scale
            0 (3 * (scale : Int)) 0 scale)) :
    ∀ epsilon : Real, 0 < epsilon → ∀ᶠ blocks in atTop,
      -Real.log
          (fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (4 * scale + 1)
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height ≤
        -Real.log
            (fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) /
          (2 * (scale + 1) : Real) + epsilon := by
  apply fkRectWindingBlock_sourceBarrier_eventualUpper_of_eventuallyDualPullback_mul_pow
    k scale (4 * scale + 1) (by omega) (by omega) hq
      (fkRectPositiveBandBarrierConstant_pos k scale hq)
      (pow_pos (fkRectDevelopedReflectedEndpointLowerOf_pos
        hcrossingFloor scale) 4)
      (fkRectWindingBlock_eventually_dualPullbackLower_of_horizontalCrossingFloor
        k scale hscale hwidth hq hcrossingFloor hcross)



theorem fkRectWindingBlock_eventually_dualPullbackLower_of_horizontalCrossing
    (k scale : Nat) (hscale : 6 ≤ scale)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    {q : Real} (hq : 1 ≤ q)
    (hcross : ∀ᶠ blocks in atTop,
      1 / (2 * (1 + q)) ≤
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            (fkRectWindingBlockVerticalFamily k scale blocks) scale
            0 (3 * (scale : Int)) 0 scale)) :
    ∀ᶠ blocks in atTop,
      fkRectPositiveBandBarrierConstant k scale q *
          (fkRectDevelopedReflectedEndpointLower q scale ^ 4) ^
            (blocks + 1) ≤
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDualPullbackSourceLeftBarrier
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (4 * scale + 1)
            (fkRectUnitLeftBarrierGap
              (fkRectWindingBlockVerticalFamily k scale blocks))) := by
  simpa [fkRectDevelopedReflectedEndpointLower] using
    (fkRectWindingBlock_eventually_dualPullbackLower_of_horizontalCrossingFloor
      k scale hscale hwidth hq
        (show 0 < 1 / (2 * (1 + q)) by positivity) hcross)


theorem fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossing
    (k scale : Nat) (hscale : 6 ≤ scale)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    {q : Real} (hq : 1 ≤ q)
    (hcross : ∀ᶠ blocks in atTop,
      1 / (2 * (1 + q)) ≤
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            (fkRectWindingBlockVerticalFamily k scale blocks) scale
            0 (3 * (scale : Int)) 0 scale)) :
    ∀ epsilon : Real, 0 < epsilon → ∀ᶠ blocks in atTop,
      -Real.log
          (fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (4 * scale + 1)
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height ≤
        -Real.log
            (fkRectDevelopedReflectedEndpointLower q scale ^ 4) /
          (2 * (scale + 1) : Real) + epsilon := by
  simpa [fkRectDevelopedReflectedEndpointLower] using
    (fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossingFloor
      k scale hscale hwidth hq
        (show 0 < 1 / (2 * (1 + q)) by positivity) hcross)

end

end StatMech.FrontierD
