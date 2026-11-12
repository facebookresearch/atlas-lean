/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryVerticalFlux
import Code.FrontierD.FKRectChargeOneModeComparison
import Code.FrontierD.FKRectBalancedSectorNormalization
import Code.FrontierD.FKRectRandomClusterEventFKG
import Code.FrontierD.FKRectSourceSeamWindingUpper



open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkMedialLoopCanonicalVerticalFlux_ne_zero_of_turn_eq_zero_of_exists
    (R : FKRectTorus) (omega : R.Configuration)
    (hvertical : ∃ C : FKMedialLoop R.medialTorus
        (fkRectConfigurationToMedialPairing R omega),
      fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) C ≠ 0)
    (D : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (hDturn : FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) D = 0) :
    fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) D ≠ 0 := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  obtain ⟨C, hCflux⟩ := hvertical
  obtain ⟨A, hA⟩ := (fkMedialBlackBoundaryCycleToLoop_bijective pairing).2 C
  induction A using Quot.ind with
  | _ c =>
      change (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
        c.1 = C at hA
      obtain ⟨d, hdComponent, hdNonzero⟩ :=
        exists_nonzero_primalBoundaryWinding_of_zeroTurn R omega D hDturn
      have hCvertical : (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega c)).2 ≠ 0 := by
        have hflux := fkMedialLoopCanonicalVerticalFlux_eq_neg_blackBoundaryWinding
          R omega c
        change fkMedialLoopCanonicalVerticalFlux pairing
            ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk c.1) =
          _ at hflux
        rw [hA] at hflux
        intro hzero
        apply hCflux
        rw [hflux, hzero, neg_zero]
      intro hDflux
      have hDvertical : (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 := by
        have hflux := fkMedialLoopCanonicalVerticalFlux_eq_neg_blackBoundaryWinding
          R omega d
        change fkMedialLoopCanonicalVerticalFlux pairing
            ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d.1) =
          _ at hflux
        rw [hdComponent] at hflux
        rw [hDflux] at hflux
        exact neg_eq_zero.mp hflux.symm
      have hDhorizontal : (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 ≠ 0 := by
        intro hzero
        apply hdNonzero
        exact Prod.ext hzero hDvertical
      have hdep :=
        fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
          R omega (fkRectBlackBoundaryPrimalCycleWalk R omega c) d.1
      rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
        R omega d] at hdep
      unfold FKRectWindingIndependent at hdep
      push Not at hdep
      simp only [Prod.smul_fst, Prod.smul_snd] at hdep
      simp only [nsmul_eq_mul] at hdep
      rw [hDvertical] at hdep
      simp only [mul_zero, zero_mul, sub_zero] at hdep
      let m := permOrbitVisitCount (fkMedialBoundaryStep pairing) d.1 d.1
      have hm : (m : Int) ≠ 0 := by
        exact_mod_cast (permOrbitVisitCount_self_pos
          (fkMedialBoundaryStep pairing) d.1).ne'
      exact (mul_ne_zero (mul_ne_zero hm hDhorizontal) hCvertical) hdep



theorem fkRectZeroTurnLoopCount_le_two_of_windingNumber_eq_one
    (R : FKRectTorus) (omega : R.Configuration)
    (hU : fkRectUnorientedVerticalWindingNumber R omega = 1) :
    fkRectZeroTurnLoopCount R omega ≤ 2 := by
  classical
  let pairing := fkRectConfigurationToMedialPairing R omega
  have hhalf : fkMedialUnorientedVerticalWindingTotal pairing / 2 = 1 := by
    simpa [fkRectUnorientedVerticalWindingNumber,
      fkRectUnorientedVerticalWindingTotal, pairing] using hU
  have htotal : fkMedialUnorientedVerticalWindingTotal pairing = 2 := by
    calc
      fkMedialUnorientedVerticalWindingTotal pairing =
          2 * (fkMedialUnorientedVerticalWindingTotal pairing / 2) :=
        (two_mul_half_fkMedialUnorientedVerticalWindingTotal pairing).symm
      _ = 2 := by rw [hhalf]
  have hvertical : ∃ C : FKMedialLoop R.medialTorus pairing,
      fkMedialLoopCanonicalVerticalFlux pairing C ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hzero : fkMedialUnorientedVerticalWindingTotal pairing = 0 := by
      unfold fkMedialUnorientedVerticalWindingTotal
      apply Finset.sum_eq_zero
      intro C hC
      rw [hnone C, Int.natAbs_zero]
    omega
  calc
    fkRectZeroTurnLoopCount R omega ≤
        (fkMedialVerticallyWindingComponents pairing).card := by
      unfold fkRectZeroTurnLoopCount fkMedialVerticallyWindingComponents
      apply Finset.card_le_card
      intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
      exact fkMedialLoopCanonicalVerticalFlux_ne_zero_of_turn_eq_zero_of_exists
        R omega hvertical C hC
    _ ≤ fkMedialUnorientedVerticalWindingTotal pairing :=
      card_fkMedialVerticallyWindingComponents_le_total pairing
    _ = 2 := htotal



theorem windingOneResidual_lower
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration)
    (hU : fkRectUnorientedVerticalWindingNumber R omega = 1) :
    (2 / Real.sqrt q) ^ 2 / q ≤ fkRectZeroTurnEulerResidual R q omega := by
  let a : Real := 2 / Real.sqrt q
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    apply (div_le_one (Real.sqrt_pos.2 (by linarith))).2
    have hq0 : 0 ≤ q := by linarith
    nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
  have hcount := fkRectZeroTurnLoopCount_le_two_of_windingNumber_eq_one
    R omega hU
  have hpow : a ^ 2 ≤ a ^ fkRectZeroTurnLoopCount R omega :=
    pow_le_pow_of_le_one ha0 ha1 hcount
  have hs : fkRectNetIndicator R omega ≤ 1 :=
    fkRectNetIndicator_le_one R omega
  rw [fkRectZeroTurnEulerResidual_eq_netIndicator R hq]
  have hqpos : 0 < q := by linarith
  have hqpow : q ^ fkRectNetIndicator R omega ≤ q := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ q) hs
  exact div_le_div₀ (pow_nonneg ha0 _) hpow (by positivity) hqpow




theorem windingOneResidual_mul_mass_le_area_mul_allTiltExpectation
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    ((2 / Real.sqrt q) ^ 2 / q) *
        fkRectCriticalEventMass R q
          {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} ≤
      Real.sqrt q ^ (R.width * R.height : Nat) *
        (∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega *
            (if fkRectUnorientedVerticalWindingNumber R omega = 1 then
              fkRectAllOrientedLoopTilt R q
                (sixVertexAntiferroelectricLambda
                  (fkQgt4SixVertexWeight q)) omega
            else 0)) := by
  classical
  rw [fkRectCriticalEventMass_eq_indicatorExpectation,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega homega
  by_cases hU : fkRectUnorientedVerticalWindingNumber R omega = 1
  · simp only [Set.mem_setOf_eq, hU, Set.indicator_of_mem, if_pos, mul_one]
    rw [fkRectAllOrientedLoopTilt_eq_residual_div_area_fkQgt4 R hq]
    have harea : Real.sqrt q ^ (R.width * R.height : Nat) ≠ 0 := by
      positivity
    have hcancel : Real.sqrt q ^ (R.width * R.height : Nat) *
        (fkRectCriticalRandomClusterProb R q omega *
          (fkRectZeroTurnEulerResidual R q omega /
            Real.sqrt q ^ (R.width * R.height : Nat))) =
        fkRectCriticalRandomClusterProb R q omega *
          fkRectZeroTurnEulerResidual R q omega := by
      field_simp [harea]
    rw [hcancel]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left (windingOneResidual_lower R hq omega hU)
        (fkRectCriticalRandomClusterProb_nonneg R (by linarith) omega))
  · simp [hU]




theorem windingOneResidual_mul_mass_le_modeCost_sq_mul_chargeOneRatio
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    ((2 / Real.sqrt q) ^ 2 / q) *
        fkRectCriticalEventMass R q
          {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} ≤
      fkRectChargeOneModeCost
          (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2 *
        (sixVertexTorusFixedChargePartitionSum R.medialTorus 1
              (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
          sixVertexTorusFixedChargePartitionSum R.medialTorus 0
              (Nat.zero_le _) (fkQgt4SixVertexWeight q)) := by
  let A : Real := Real.sqrt q ^ (R.width * R.height : Nat)
  let K : Real := fkRectChargeOneModeCost
    (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
  let Z1 : Real := sixVertexTorusFixedChargePartitionSum R.medialTorus 1
    (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q)
  let Z0 : Real := sixVertexTorusFixedChargePartitionSum R.medialTorus 0
    (Nat.zero_le _) (fkQgt4SixVertexWeight q)
  let Z : Real := fkRectCriticalReducedZ R q
  let B : Real := fkRectBalancedSectorNormalization R q
  let W : Real := ∑ omega : R.Configuration,
    fkRectCriticalRandomClusterProb R q omega *
      (if fkRectUnorientedVerticalWindingNumber R omega = 1 then
        fkRectAllOrientedLoopTilt R q
          (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) omega
      else 0)
  have hsource : ((2 / Real.sqrt q) ^ 2 / q) *
        fkRectCriticalEventMass R q
          {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} ≤
      A * W := by
    exact windingOneResidual_mul_mass_le_area_mul_allTiltExpectation R hq
  have hmode : W ≤ K ^ 2 * (Z1 / Z) := by
    simpa [W, K, Z1, Z] using
      (windingOneAllTiltExpectation_le_modeCost_sq_mul_chargeOneRatio R hq)
  have hA : 0 ≤ A := by positivity
  have hZ1 : 0 < Z1 := by
    dsimp [Z1]
    rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
    exact sixVertexSector_trace_pow_pos
      ((Nat.sub_le _ _).trans (Nat.div_le_self R.medialTorus.width 2))
      (by linarith [two_lt_fkQgt4SixVertexWeight hq])
      R.medialTorus.height
  have hZ0 : 0 < Z0 := by
    dsimp [Z0]
    rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
    exact sixVertexSector_trace_pow_pos
      (Nat.div_le_self R.medialTorus.width 2)
      (by linarith [two_lt_fkQgt4SixVertexWeight hq])
      R.medialTorus.height
  have hratio : 0 < Z1 / Z0 := div_pos hZ1 hZ0
  have hcommon : A * (Z1 / Z) = (Z1 / Z0) * B := by
    dsimp [A, Z1, Z0, Z, B]
    unfold fkRectBalancedSectorNormalization
    have hZ0 : sixVertexTorusFixedChargePartitionSum R.medialTorus 0
        (Nat.zero_le _) (fkQgt4SixVertexWeight q) ≠ 0 := by
      simpa [Z0] using hZ0.ne'
    have hZ : fkRectCriticalReducedZ R q ≠ 0 :=
      (fkRectCriticalReducedZ_pos R (by linarith)).ne'
    field_simp [hZ0, hZ]
  calc
    ((2 / Real.sqrt q) ^ 2 / q) *
          fkRectCriticalEventMass R q
            {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} ≤
        A * W := hsource
    _ ≤ A * (K ^ 2 * (Z1 / Z)) :=
      mul_le_mul_of_nonneg_left hmode hA
    _ = K ^ 2 * ((Z1 / Z0) * B) := by rw [← hcommon]; ring
    _ ≤ K ^ 2 * (Z1 / Z0) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg K)
      apply mul_le_of_le_one_right hratio.le
      exact fkRectBalancedSectorNormalization_le_one R hq
    _ = _ := by rfl




theorem fkRectSource_mul_windingResidual_le_modeCost_sq_mul_chargeOneRatio
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 4 < q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    ((2 / Real.sqrt q) ^ 2 / q) *
        (FK.cFE (fkRectCriticalP q) q *
          (∏ xy ∈ t,
            FK.twoPointFun
              (fkRectInducedGraph R
                (fkRectRightStripBand R cut 1 (R.height - 1)))
              (fkRectCriticalP q) q xy.1 xy.2) *
          fkRectCriticalEventMass R q
            (fkRectSourceLeftBarrier R leftRight gap)) ≤
      fkRectChargeOneModeCost
          (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2 *
        (sixVertexTorusFixedChargePartitionSum R.medialTorus 1
              (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
          sixVertexTorusFixedChargePartitionSum R.medialTorus 0
              (Nat.zero_le _) (fkQgt4SixVertexWeight q)) := by
  have hsource := fkRectSource_barrierConnectionProduct_le_windingOneMass
    R leftRight cut hsep hleft (by linarith : 1 ≤ q) hgap x hx hchosen t hpair
  have hc : 0 ≤ (2 / Real.sqrt q) ^ 2 / q := by positivity
  exact (mul_le_mul_of_nonneg_left hsource hc).trans
    (windingOneResidual_mul_mass_le_modeCost_sq_mul_chargeOneRatio R hq)

end

end StatMech.FrontierD
