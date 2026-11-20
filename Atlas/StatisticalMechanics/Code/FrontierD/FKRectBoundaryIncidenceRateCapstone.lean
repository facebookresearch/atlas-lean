/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKQgt4PIMSTwoByOnePhaseAssembly
import Code.FrontierD.FKQgt4PhaseFinalAssembly
import Code.FrontierD.FKRectHorizontalCylinderTransverseRate



open Filter MeasureTheory Topology

namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice

noncomputable section




theorem fkQgt4_pred_exactDiagonalHalf_le_fixedChargeRate_of_normalizationVertical
    {q normalizationRate : Real} (hq : 4 < q)
    (r : Nat) (hr : 2 <= r) (k : Nat)
    (hnormalization : Tendsto (fun m =>
      -Real.log
          (fkRectBalancedSectorNormalization
            (fkRectFixedChargeVerticalFamily r k m) q) /
        (fkRectFixedChargeVerticalFamily r k m).height)
      atTop (nhds normalizationRate)) :
    ((r - 1 : Nat) : Real) *
        (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
      -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) r (k + 1) + normalizationRate := by
  let R : Nat -> FKRectTorus :=
    fun m => fkRectFixedChargeVerticalFamily r k m
  let a : Real := FK.cFE (fkRectCriticalP q) q ^ (2 * (R 0).width)
  let b : Real := Nat.choose (R 0).width r * (R 0).width ^ (R 0).width
  have ha : 0 < a := by
    exact pow_pos (FK.cFE_pos
      (fkRectCriticalP_pos (by linarith : (0 : Real) < q))
      (fkRectCriticalP_lt_one (by linarith : (0 : Real) < q))
      (by linarith : (1 : Real) <= q)) _
  have hb : 0 < b := by
    dsimp [b, R]
    exact mul_pos
      (by
        exact_mod_cast Nat.choose_pos (by omega))
      (by positivity)
  have hheight : Tendsto (fun m => (R m).height) atTop atTop := by
    simpa only [R, fkRectFixedChargeVerticalFamily_height] using
      tendsto_fkRectFixedChargeVerticalFamily_height
  have hcorr : forall m, 0 < Real.sqrt
      (fkQgt4CriticalFreeExactDiagonalTwoPoint hq ((R m).height - 1)) := by
    intro m
    exact Real.sqrt_pos.2
      (fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq ((R m).height - 1))
  have htail : forall m, 0 < fkRectCriticalWindingTailMass (R m) q r := by
    intro m
    apply fkRectCriticalWindingTailMass_pos_of_fixedCharge (R m) hq r
    exact fkRectFixedChargeVerticalFamily_charge_le r k m
  have hpoint (m : Nat) :
      ((r - 1 : Nat) : Real) *
          (-Real.log (Real.sqrt
            (fkQgt4CriticalFreeExactDiagonalTwoPoint hq
              ((R m).height - 1))) / ((R m).height : Real)) <=
        (-Real.log
            (sixVertexTorusFixedChargePartitionSum (R m).medialTorus r
                  (fkRectFixedChargeVerticalFamily_charge_le r k m)
                  (fkQgt4SixVertexWeight q) /
              sixVertexTorusFixedChargePartitionSum (R m).medialTorus 0
                  (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
            ((R m).height : Real) +
          -Real.log (fkRectBalancedSectorNormalization (R m) q) /
            ((R m).height : Real)) +
        (Real.log b - Real.log a) / ((R m).height : Real) := by
    have hbound : a * fkRectCriticalWindingTailMass (R m) q r <=
        b * Real.sqrt
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq
            ((R m).height - 1)) ^ (r - 1) := by
      have h :=
        fkRectCriticalWindingTailMass_cFE_le_crossingPrefactor_mul_sqrtExact
          hq (R m) r (by omega)
          (fkRectWindingTailForcesHorizontalCylinderCrossings_unconditional
            (R m) r)
      simpa [a, b, R] using h
    have hpow :=
      StatMech.Probability.pow_negLog_div_le_negLog_div_add_const_of_mul_le_mul_pow
        ha hb (htail m) (hcorr m) (R m).height_pos hbound
    have hfixed := windingTail_negLogRate_le_fixedCharge_add_normalizationDefect
      (R m) hq r (fkRectFixedChargeVerticalFamily_charge_le r k m)
    linarith
  have hleft :=
    (fkQgt4_sqrtExactDiagonal_heightSubOne_negLogRate_tendsto hq R hheight).const_mul
      ((r - 1 : Nat) : Real)
  have hcharge := fkRectFixedCharge_vertical_negLogRatio_tendsto
    (by linarith [two_lt_fkQgt4SixVertexWeight hq] :
      0 < fkQgt4SixVertexWeight q) r k
  have hconst : Tendsto (fun m =>
      (Real.log b - Real.log a) / ((R m).height : Real))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat
      (Real.log b - Real.log a)).comp hheight
  have hright := (hcharge.add (by simpa [R] using hnormalization)).add hconst
  have hle := le_of_tendsto_of_tendsto hleft hright (by
    filter_upwards [] with m
    simpa [R] using hpoint m)
  simpa using hle




theorem fkQgt4_fixedCharge_bound_of_normalizationVertical_unconditional
    {q : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (hnormalization : forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) *
        (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap hq r (by omega))
  filter_upwards [] with k
  simpa using
    (fkQgt4_pred_exactDiagonalHalf_le_fixedChargeRate_of_normalizationVertical
      hq r hr k (hnormalization k))



theorem fkQgt4_fixedCharge_bound_of_normalizationLimits_unconditional
    {q : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (normalizationRate : Nat -> Real)
    (hnormalizationVertical : forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (normalizationRate k)))
    (hnormalizationHorizontal : Tendsto normalizationRate atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) *
        (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  have hpoint (k : Nat) :
      ((r - 1 : Nat) : Real) *
          (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
        -sixVertexFixedChargeLogRatio
            (fkQgt4SixVertexWeight q) r (k + 1) + normalizationRate k :=
    fkQgt4_pred_exactDiagonalHalf_le_fixedChargeRate_of_normalizationVertical
      hq r hr k (hnormalizationVertical k)
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds
    ((tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap hq r (by omega)).add
      hnormalizationHorizontal)
    (Filter.Eventually.of_forall hpoint)
  simpa using hle





theorem fkQgt4_fixedCharge_bound_of_verticalWindingTailLimits_unconditional
    {q : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (windingRate normalizationRate : Nat -> Real)
    (hwindVertical : forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k m) q r) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (windingRate k)))
    (hnormalizationVertical : forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (normalizationRate k)))
    (hnormalizationHorizontal :
      Tendsto normalizationRate atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) *
        (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  have hheight : Tendsto (fun m =>
      (fkRectFixedChargeVerticalFamily r 0 m).height) atTop atTop := by
    simpa only [fkRectFixedChargeVerticalFamily_height] using
      tendsto_fkRectFixedChargeVerticalFamily_height
  have hlower (k : Nat) :
      ((r - 1 : Nat) : Real) *
          (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <=
        windingRate k := by
    apply fkQgt4_mul_pred_exactDiagonalHalf_le_windingTailRate_unconditional
      hq (fun m => fkRectFixedChargeVerticalFamily r k m)
        (2 * (r + k + 2)) r (by omega) (by omega)
    · intro m
      exact fkRectFixedChargeVerticalFamily_width r k m
    · simpa only [fkRectFixedChargeVerticalFamily_height] using hheight
    · exact hwindVertical k
  have hfixedWidth (k : Nat) :
      windingRate k <=
        -sixVertexFixedChargeLogRatio
          (fkQgt4SixVertexWeight q) r (k + 1) + normalizationRate k := by
    exact windingTailRate_le_fixedChargeRate_add_normalizationRate_of_tendsto
      (fun m => fkRectFixedChargeVerticalFamily r k m)
      (q := q) (windingRate := windingRate k)
      (chargeRate := -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) r (k + 1))
      (normalizationRate := normalizationRate k)
      hq r
      (fun m => fkRectFixedChargeVerticalFamily_charge_le r k m)
      (hwindVertical k)
      (fkRectFixedCharge_vertical_negLogRatio_tendsto
        (by linarith [two_lt_fkQgt4SixVertexWeight hq] :
          0 < fkQgt4SixVertexWeight q) r k)
      (hnormalizationVertical k)
  have hle := le_of_tendsto_of_tendsto
    (tendsto_const_nhds : Tendsto (fun _ : Nat =>
      ((r - 1 : Nat) : Real) *
        (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) atTop
          (nhds (((r - 1 : Nat) : Real) *
            (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2))))
    ((tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap hq r (by omega)).add
      hnormalizationHorizontal)
    (Filter.Eventually.of_forall (fun k => (hlower k).trans (hfixedWidth k)))
  simpa using hle



theorem fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_verticalLimits
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (windingRate normalizationRate : Nat -> Nat -> Real)
    (hwindVertical : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k m) q r) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (windingRate r k)))
    (hnormalizationVertical : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (normalizationRate r k)))
    (hnormalizationHorizontal : forall r : Nat, 2 <= r ->
      Tendsto (normalizationRate r) atTop (nhds 0)) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge
    hq hhard hcross
  intro r hr
  exact fkQgt4_fixedCharge_bound_of_verticalWindingTailLimits_unconditional
    hq r hr (windingRate r) (normalizationRate r)
      (hwindVertical r hr) (hnormalizationVertical r hr)
      (hnormalizationHorizontal r hr)



theorem fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_normalizationVertical
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hnormalization : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds 0)) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge
    hq hhard hcross
  intro r hr
  exact fkQgt4_fixedCharge_bound_of_normalizationVertical_unconditional
    hq r hr (hnormalization r hr)



theorem fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_normalizationLimits
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (normalizationRate : Nat -> Nat -> Real)
    (hnormalizationVertical : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (normalizationRate r k)))
    (hnormalizationHorizontal : forall r : Nat, 2 <= r ->
      Tendsto (normalizationRate r) atTop (nhds 0)) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge
    hq hhard hcross
  intro r hr
  exact fkQgt4_fixedCharge_bound_of_normalizationLimits_unconditional
    hq r hr (normalizationRate r)
      (hnormalizationVertical r hr) (hnormalizationHorizontal r hr)



theorem fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_verticalLimits
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (windingRate normalizationRate : Nat -> Nat -> Real)
    (hwindVertical : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k m) q r) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (windingRate r k)))
    (hnormalizationVertical : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (normalizationRate r k)))
    (hnormalizationHorizontal : forall r : Nat, 2 <= r ->
      Tendsto (normalizationRate r) atTop (nhds 0)) :
    let hp := (BeffaraDC.selfDualPoint_mem_Ioo
      (by linarith : (0 : Real) < q)).1
    let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
      (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          MeasureTheory.ProbabilityMeasure
            (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) :
        MeasureTheory.Measure
          (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))))
          (hasInfiniteClusterEvent 2) = 1 ∧
      Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q)) ∧
      0 < fkQgt4SixVertexGapRate q := by
  apply fkQgt4_discontinuity_of_winding hq
  exact fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_verticalLimits
    hq hhard hcross windingRate normalizationRate hwindVertical
      hnormalizationVertical hnormalizationHorizontal



theorem fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_normalizationVertical
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hnormalization : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds 0)) :
    let hp := (BeffaraDC.selfDualPoint_mem_Ioo
      (by linarith : (0 : Real) < q)).1
    let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
      (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2))))
          (hasInfiniteClusterEvent 2) = 1 ∧
      Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q)) ∧
      0 < fkQgt4SixVertexGapRate q := by
  apply fkQgt4_discontinuity_of_winding hq
  exact
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_normalizationVertical
      hq hhard hcross hnormalization



theorem fkQgt4_critical_potts_phases_of_evenTwoByOneCrossingFloor_and_verticalLimits
    (q : Nat) [NeZero q] (hq : 4 < q) (J : Real) (hJ : 0 < J)
    {hardFloor : Real} (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (windingRate normalizationRate : Nat -> Nat -> Real)
    (hwindVertical : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k m) q r) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (windingRate r k)))
    (hnormalizationVertical : forall r : Nat, 2 <= r -> forall k : Nat,
      Tendsto (fun m =>
        -Real.log
            (fkRectBalancedSectorNormalization
              (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
        atTop (nhds (normalizationRate r k)))
    (hnormalizationHorizontal : forall r : Nat, 2 <= r ->
      Tendsto (normalizationRate r) atTop (nhds 0)) :
    ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q))
      (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q))
      (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat),
      Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q
          (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧
      (forall b, StrictMono (phiWired b) ∧
        Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b
          (pottsSelfDualInverseTemperature q J) J)
          atTop (nhds (muWired b))) ∧
      (forall b, muFree ≠ muWired b) ∧
      forall b c, b ≠ c -> muWired b ≠ muWired c := by
  let hqR : (4 : Real) < q := by exact_mod_cast hq
  apply fkQgt4_critical_potts_phases_of_winding q hq J hJ
  exact fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_verticalLimits
    hqR hhard hcross windingRate normalizationRate hwindVertical
      hnormalizationVertical hnormalizationHorizontal

end

end StatMech.FrontierD
