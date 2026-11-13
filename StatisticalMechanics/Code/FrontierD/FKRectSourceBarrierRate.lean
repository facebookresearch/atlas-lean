/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectIndexedPatternPushforward
import Code.FrontierD.FKRectWindingBlockSource



open Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem fkRectCriticalEventMass_auxiliaryChain_ge_pow
    (R : FKRectTorus) {q a : Real} (hq : 1 <= q) (ha : 0 <= a)
    {ι : Type*} (s : Finset ι) (E : ι -> Set R.Configuration)
    (hE : ∀ i ∈ s, IsIncreasing (E i))
    (hlower : ∀ i ∈ s, a <= fkRectCriticalEventMass R q (E i)) :
    a ^ s.card <= fkRectCriticalEventMass R q
      (fkRectFiniteEventIntersection s E) := by
  calc
    a ^ s.card = ∏ _i ∈ s, a := by simp
    _ <= ∏ i ∈ s, fkRectCriticalEventMass R q (E i) :=
      Finset.prod_le_prod (fun _ _ => ha) hlower
    _ <= _ := fkRectCriticalEventMass_prod_le_finiteIntersection
      R hq s E hE



theorem fkRectCriticalEventMass_auxiliaryDecreasingChain_ge_pow
    (R : FKRectTorus) {q a : Real} (hq : 1 <= q) (ha : 0 <= a)
    {ι : Type*} (s : Finset ι) (E : ι -> Set R.Configuration)
    (hE : ∀ i ∈ s, IsDecreasing (E i))
    (hlower : ∀ i ∈ s, a <= fkRectCriticalEventMass R q (E i)) :
    a ^ s.card <= fkRectCriticalEventMass R q
      (fkRectFiniteEventIntersection s E) := by
  calc
    a ^ s.card = ∏ _i ∈ s, a := by simp
    _ <= ∏ i ∈ s, fkRectCriticalEventMass R q (E i) :=
      Finset.prod_le_prod (fun _ _ => ha) hlower
    _ <= _ := fkRectCriticalEventMass_prod_le_finiteIntersection_decreasing
      R hq s E hE




theorem fkRectCritical_cFE_pow_width_mul_auxiliary_le_sourceBarrier
    (R : FKRectTorus) (leftRight : Nat) {q : Real} (hq : 1 <= q)
    (gap : R.EdgeIndex) (A : Set R.Configuration)
    (hforce : ∀ omega ∈ A,
      fkRectForceIndexedPattern R (fkRectHorizontalCutEdges R)
          (fkRectAllButOneOpenConfiguration R gap) omega ∈
        fkRectNoLeftStripCrossingEvent R leftRight) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
        fkRectCriticalEventMass R q A <=
      fkRectCriticalEventMass R q
        (fkRectSourceLeftBarrier R leftRight gap) := by
  let I := fkRectHorizontalCutEdges R
  let eta := fkRectAllButOneOpenConfiguration R gap
  let target := fkRectSourceLeftBarrier R leftRight gap
  have hsubset : A ⊆ fkRectForceIndexedPattern R I eta ⁻¹' target := by
    intro omega homega
    constructor
    · exact hforce omega homega
    · intro edge hedge
      exact fkRectForceIndexedPattern_of_mem R eta omega hedge
  have hmono := fkRectCriticalEventMass_mono R
    (zero_lt_one.trans_le hq) hsubset
  have hc : 0 <= FK.cFE (fkRectCriticalP q) q :=
    fkRectCritical_cFE_nonneg hq
  have hmul := mul_le_mul_of_nonneg_left hmono
    (pow_nonneg hc (2 * R.width))
  have hpattern :=
    fkRectCritical_cFE_pow_mul_forceIndexedPattern_preimage_le_event
      R hq I eta target
  rw [fkRectHorizontalCutEdges_card] at hpattern
  exact hmul.trans hpattern




theorem fkRectCritical_cFE_pow_width_mul_auxiliaryPow_le_sourceBarrier
    (R : FKRectTorus) (leftRight blocks : Nat)
    {q a : Real} (hq : 1 <= q)
    (gap : R.EdgeIndex) (A : Set R.Configuration)
    (haux : a ^ blocks <= fkRectCriticalEventMass R q A)
    (hforce : ∀ omega ∈ A,
      fkRectForceIndexedPattern R (fkRectHorizontalCutEdges R)
          (fkRectAllButOneOpenConfiguration R gap) omega ∈
        fkRectNoLeftStripCrossingEvent R leftRight) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) * a ^ blocks <=
      fkRectCriticalEventMass R q
        (fkRectSourceLeftBarrier R leftRight gap) := by
  have hc : 0 <= FK.cFE (fkRectCriticalP q) q :=
    fkRectCritical_cFE_nonneg hq
  exact (mul_le_mul_of_nonneg_left haux
    (pow_nonneg hc (2 * R.width))).trans
      (fkRectCritical_cFE_pow_width_mul_auxiliary_le_sourceBarrier
        R leftRight hq gap A hforce)


theorem fkRectSourceBarrier_negLogRate_le_of_auxiliaryPow
    (R : FKRectTorus) (leftRight blocks : Nat)
    (hone : 1 <= leftRight) (hleft : leftRight + 1 < R.width)
    {q a : Real} (hq : 1 <= q) (ha : 0 < a)
    (A : Set R.Configuration)
    (haux : a ^ blocks <= fkRectCriticalEventMass R q A)
    (hforce : ∀ omega ∈ A,
      fkRectForceIndexedPattern R (fkRectHorizontalCutEdges R)
          (fkRectAllButOneOpenConfiguration R
            (fkRectUnitLeftBarrierGap R)) omega ∈
        fkRectNoLeftStripCrossingEvent R leftRight) :
    -Real.log (fkRectCriticalEventMass R q
        (fkRectSourceLeftBarrier R leftRight
          (fkRectUnitLeftBarrierGap R))) / R.height <=
      (blocks : Real) * (-Real.log a) / R.height +
        (2 * R.width : Nat) *
          (-Real.log (FK.cFE (fkRectCriticalP q) q)) / R.height := by
  let c := FK.cFE (fkRectCriticalP q) q
  let B := fkRectCriticalEventMass R q
    (fkRectSourceLeftBarrier R leftRight (fkRectUnitLeftBarrierGap R))
  have hc : 0 < c := by
    dsimp [c]
    exact FK.cFE_pos
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq
  have hB : 0 < B := by
    dsimp [B]
    exact fkRectCriticalEventMass_pos_of_mem R (zero_lt_one.trans_le hq) _
      (fkRectUnitLeftBarrierConfiguration R)
      (fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le
        R leftRight hone hleft)
  have hlower : c ^ (2 * R.width) * a ^ blocks <= B := by
    simpa [c, B] using
      (fkRectCritical_cFE_pow_width_mul_auxiliaryPow_le_sourceBarrier
        R leftRight blocks hq (fkRectUnitLeftBarrierGap R) A haux hforce)
  have hlog := Real.log_le_log
    (mul_pos (pow_pos hc _) (pow_pos ha _)) hlower
  rw [Real.log_mul (pow_pos hc _).ne' (pow_pos ha _).ne',
    Real.log_pow, Real.log_pow] at hlog
  have hnum : -Real.log B <=
      (blocks : Real) * (-Real.log a) +
        (2 * R.width : Nat) * (-Real.log c) := by
    linarith
  have hh : 0 <= (R.height : Real) := by positivity
  calc
    -Real.log B / R.height <=
        ((blocks : Real) * (-Real.log a) +
          (2 * R.width : Nat) * (-Real.log c)) / R.height :=
      div_le_div_of_nonneg_right hnum hh
    _ = (blocks : Real) * (-Real.log a) / R.height +
        (2 * R.width : Nat) * (-Real.log c) / R.height := by ring
    _ = _ := by rfl




theorem fkRectWindingBlock_sourceBarrier_eventualUpper_of_auxiliary
    (k scale leftRight : Nat) (hone : 1 <= leftRight)
    (hleft : leftRight + 1 < 2 * (k + 3))
    {q a : Real} (hq : 1 <= q) (ha : 0 < a)
    (A : forall blocks,
      Set (fkRectWindingBlockVerticalFamily k scale blocks).Configuration)
    (haux : forall blocks,
      a ^ (blocks + 1) <=
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q (A blocks))
    (hforce : forall blocks,
      ∀ omega ∈ A blocks,
        fkRectForceIndexedPattern
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (fkRectHorizontalCutEdges
              (fkRectWindingBlockVerticalFamily k scale blocks))
            (fkRectAllButOneOpenConfiguration
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks))) omega ∈
          fkRectNoLeftStripCrossingEvent
            (fkRectWindingBlockVerticalFamily k scale blocks) leftRight) :
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
  let seamConstant : Real := (4 * (k + 3) : Nat) *
    (-Real.log (FK.cFE (fkRectCriticalP q) q))
  let seamCost : Nat -> Real := fun blocks =>
    seamConstant /
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
  have hseam : Tendsto seamCost atTop (nhds 0) := by
    exact hheight.const_div_atTop seamConstant
  have hupper := hblock.add hseam
  have hevent : ∀ᶠ blocks in atTop,
      blockCost blocks + seamCost blocks <
        -Real.log a / (2 * (scale + 1) : Real) + epsilon :=
    (tendsto_order.1 hupper).2 _ (by linarith)
  filter_upwards [hevent] with blocks hcost
  have hfinite := fkRectSourceBarrier_negLogRate_le_of_auxiliaryPow
    (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (blocks + 1)
    hone hleft hq ha (A blocks) (haux blocks) (hforce blocks)
  change -Real.log
          (fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) /
        (fkRectWindingBlockVerticalFamily k scale blocks).height <=
      -Real.log a / (2 * (scale + 1) : Real) + epsilon
  dsimp [blockCost, seamCost, seamConstant] at hcost
  simp only [fkRectWindingBlockVerticalFamily_width,
    fkRectWindingBlockVerticalFamily_height] at hfinite ⊢
  rw [show 2 * (2 * (k + 3)) = 4 * (k + 3) by omega] at hfinite
  linarith



theorem fkRectWindingBlock_chargeOneRate_le_connectionAndAuxiliary
    {q connectionLower auxiliaryLower : Real} (hq : 4 < q)
    (hconnectionPos : 0 < connectionLower)
    (hconnectionOne : connectionLower <= 1)
    (hauxiliaryPos : 0 < auxiliaryLower)
    (k scale leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < 2 * (k + 3))
    (x : Fin (2 * (k + 3))) (hx : cut <= x.val)
    (hblock : forall blocks,
      ∀ xy ∈ connectionPathPairs (blocks + 1)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx),
        connectionLower <= FK.twoPointFun
          (fkRectInducedGraph
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (fkRectRightStripBand
              (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
              ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2)
    (A : forall blocks,
      Set (fkRectWindingBlockVerticalFamily k scale blocks).Configuration)
    (haux : forall blocks,
      auxiliaryLower ^ (blocks + 1) <=
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q (A blocks))
    (hforce : forall blocks,
      ∀ omega ∈ A blocks,
        fkRectForceIndexedPattern
            (fkRectWindingBlockVerticalFamily k scale blocks)
            (fkRectHorizontalCutEdges
              (fkRectWindingBlockVerticalFamily k scale blocks))
            (fkRectAllButOneOpenConfiguration
              (fkRectWindingBlockVerticalFamily k scale blocks)
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks))) omega ∈
          fkRectNoLeftStripCrossingEvent
            (fkRectWindingBlockVerticalFamily k scale blocks) leftRight) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <=
      -Real.log connectionLower / (2 * (scale + 1) : Real) +
        -Real.log auxiliaryLower / (2 * (scale + 1) : Real) := by
  apply fkRectWindingBlock_chargeOneRate_le_blockAndBarrier
    hq hconnectionPos hconnectionOne k scale leftRight cut hone hsep hleft
    x hx hblock
  exact fkRectWindingBlock_sourceBarrier_eventualUpper_of_auxiliary
    k scale leftRight hone hleft (by linarith : 1 <= q) hauxiliaryPos
    A haux hforce

end

end StatMech.FrontierD
