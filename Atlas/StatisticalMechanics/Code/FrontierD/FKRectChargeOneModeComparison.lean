/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.BoolModeForcedSum
import Code.FrontierD.FKRectTorusWindingCountBridge










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance medialLoopDecidableEq {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) :
    DecidableEq (FKMedialLoop T pairing) := Classical.decEq _


def fkRectComponentModeWeight {T : EvenTorus}
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (C : FKMedialLoop T pairing) (b : Bool) : Real :=
  if b then
    Real.exp (-(lam / 4) *
      FKMedialTurningFiber.canonicalComponentTurn pairing C)
  else
    Real.exp ((lam / 4) *
      FKMedialTurningFiber.canonicalComponentTurn pairing C)


def fkRectChargeOneModeCost (lam : Real) : Real :=
  1 + Real.exp (2 * lam)

theorem fkRectChargeOneModeCost_one_le (lam : Real) :
    1 <= fkRectChargeOneModeCost lam := by
  unfold fkRectChargeOneModeCost
  exact le_add_of_nonneg_right (Real.exp_pos _).le

private theorem exp_add_exp_neg_le_cost_mul_exp_neg
    {lam : Real} :
    Real.exp lam + Real.exp (-lam) <=
      fkRectChargeOneModeCost lam * Real.exp (-lam) := by
  unfold fkRectChargeOneModeCost
  rw [add_mul, one_mul, ← Real.exp_add]
  ring_nf
  exact le_rfl

private theorem exp_add_exp_neg_le_cost_mul_exp
    {lam : Real} (hlam : 0 <= lam) :
    Real.exp lam + Real.exp (-lam) <=
      fkRectChargeOneModeCost lam * Real.exp lam := by
  unfold fkRectChargeOneModeCost
  rw [add_mul, one_mul, ← Real.exp_add]
  have h : Real.exp (-lam) <= Real.exp (3 * lam) :=
    Real.exp_le_exp.mpr (by linarith)
  have h' : Real.exp (-lam) <= Real.exp (2 * lam + lam) := by
    simpa only [show 2 * lam + lam = 3 * lam by ring] using h
  linarith



theorem componentModeWeight_sum_le_cost_mul
    (R : FKRectTorus) (lam : Real) (hlam : 0 <= lam)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (forced : FKMedialLoop R.medialTorus pairing -> Bool)
    (C : FKMedialLoop R.medialTorus pairing) :
    fkRectComponentModeWeight lam pairing C false +
        fkRectComponentModeWeight lam pairing C true <=
      fkRectChargeOneModeCost lam *
        fkRectComponentModeWeight lam pairing C (forced C) := by
  rcases fkRectCanonicalComponentTurn_classification R pairing C with
    hzero | hfour | hnegfour
  · cases hforced : forced C <;>
      simp [fkRectComponentModeWeight, fkRectChargeOneModeCost, hzero,
        Real.one_le_exp (by positivity : 0 <= 2 * lam)]
  · cases hforced : forced C
    · simpa [fkRectComponentModeWeight, hfour, hforced] using
        exp_add_exp_neg_le_cost_mul_exp (lam := lam) hlam
    · simpa [fkRectComponentModeWeight, hfour, hforced] using
        exp_add_exp_neg_le_cost_mul_exp_neg (lam := lam)
  · cases hforced : forced C
    · simpa [fkRectComponentModeWeight, hnegfour, hforced, add_comm] using
        exp_add_exp_neg_le_cost_mul_exp_neg (lam := lam)
    · simpa [fkRectComponentModeWeight, hnegfour, hforced, add_comm] using
        exp_add_exp_neg_le_cost_mul_exp (lam := lam) hlam

private theorem fluxFilteredWeight_sum_eq_modes
    {T : EvenTorus} (lam : Real) (pairing : FKMedialLoopPairing T)
    (z : Int) :
    (∑ arrows : SixVertexArrows T,
        if fkOrientedLoopVerticalFlux T arrows = z then
          fkOrientedLoopPairingWeight lam pairing arrows
        else 0) =
      ∑ mode : (FKMedialLoop T pairing -> Bool),
        if fkOrientedLoopVerticalFlux T
            (FKMedialTurningFiber.arrowsOfMode pairing mode) = z then
          fkOrientedLoopPairingWeight lam pairing
            (FKMedialTurningFiber.arrowsOfMode pairing mode)
        else 0 := by
  classical
  let p : SixVertexArrows T -> Prop := fun arrows =>
    forall v, fkLoopPairingCompatible (pairing v) arrows v
  let f : SixVertexArrows T -> Real := fun arrows =>
    if fkOrientedLoopVerticalFlux T arrows = z then
      fkOrientedLoopPairingWeight lam pairing arrows
    else 0
  have hzero (arrows : SixVertexArrows T) (harrows : ¬ p arrows) :
      f arrows = 0 := by
    simp only [p] at harrows
    push Not at harrows
    obtain ⟨v, hv⟩ := harrows
    unfold f fkOrientedLoopPairingWeight
    split
    · apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [fkOrientedLoopLocalWeight, hv]
    · rfl
  change (∑ arrows : SixVertexArrows T, f arrows) = _
  calc
    (∑ arrows : SixVertexArrows T, f arrows) =
        ∑ arrows : SixVertexArrows T, if p arrows then f arrows else 0 := by
      apply Finset.sum_congr rfl
      intro arrows harrows
      by_cases hpa : p arrows
      · rw [if_pos hpa]
      · rw [if_neg hpa, hzero arrows hpa]
    _ = ∑ arrows ∈ (Finset.univ.filter p), f arrows := by
      symm
      simpa using Finset.sum_filter p f
    _ = ∑ arrows : {arrows : SixVertexArrows T // p arrows},
          f arrows.1 := by
      symm
      simpa using Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (SixVertexArrows T))) (p := p) f
    _ = ∑ mode : (FKMedialLoop T pairing -> Bool),
          f (FKMedialTurningFiber.arrowsOfMode pairing mode) := by
      symm
      apply Fintype.sum_equiv
        (FKMedialTurningFiber.modeEquivCompatibleArrows pairing)
      intro mode
      rfl



theorem forcedDownwardModeSum_le_chargeOneFiber
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration)
    (hU : fkRectUnorientedVerticalWindingNumber R omega = 1) :
    forcedBoolModeSum
        (fkMedialVerticallyWindingComponents
          (fkRectConfigurationToMedialPairing R omega))
        (fkMedialDownwardVerticalMode
          (fkRectConfigurationToMedialPairing R omega))
        (fkRectComponentModeWeight lam
          (fkRectConfigurationToMedialPairing R omega)) <=
      ∑ arrows : SixVertexArrows R.medialTorus,
        if fkOrientedLoopVerticalFlux R.medialTorus arrows = -2 then
          fkRectOrientedLoopWeight R lam omega arrows
        else 0 := by
  classical
  let pairing := fkRectConfigurationToMedialPairing R omega
  let S := fkMedialVerticallyWindingComponents pairing
  let down := fkMedialDownwardVerticalMode pairing
  let f := fkRectComponentModeWeight lam pairing
  have htotal : fkMedialUnorientedVerticalWindingTotal pairing = 2 := by
    have hhalf : fkMedialUnorientedVerticalWindingTotal pairing / 2 = 1 := hU
    calc
      fkMedialUnorientedVerticalWindingTotal pairing =
          2 * (fkMedialUnorientedVerticalWindingTotal pairing / 2) :=
        (two_mul_half_fkMedialUnorientedVerticalWindingTotal pairing).symm
      _ = 2 := by rw [hhalf]
  change forcedBoolModeSum S down f <=
    ∑ arrows : SixVertexArrows R.medialTorus,
      if fkOrientedLoopVerticalFlux R.medialTorus arrows = -2 then
        fkOrientedLoopPairingWeight lam pairing arrows
      else 0
  rw [fluxFilteredWeight_sum_eq_modes lam pairing (-2)]
  unfold forcedBoolModeSum
  apply Finset.sum_le_sum
  intro mode hmode
  by_cases hforced : forall C, C ∈ S -> mode C = down C
  · rw [if_pos hforced]
    have hflux :=
      fkOrientedLoopVerticalFlux_eq_downwardMode_of_eq_on_windingComponents
        pairing mode hforced
    rw [htotal] at hflux
    rw [if_pos (by simpa using hflux)]
    simpa only [f, fkRectOrientedLoopWeight] using
      (FKMedialTurningFiber.orientedLoopWeight_arrowsOfMode
        lam pairing mode).symm.le
  · rw [if_neg hforced]
    split
    · exact fkOrientedLoopPairingWeight_nonneg lam pairing _
    · exact le_rfl



theorem allOrientedLoopWeight_le_modeCost_sq_mul_chargeOneFiber
    (R : FKRectTorus) (lam : Real) (hlam : 0 <= lam)
    (omega : R.Configuration)
    (hU : fkRectUnorientedVerticalWindingNumber R omega = 1) :
    (∑ arrows : SixVertexArrows R.medialTorus,
        fkRectOrientedLoopWeight R lam omega arrows) <=
      fkRectChargeOneModeCost lam ^ 2 *
        ∑ arrows : SixVertexArrows R.medialTorus,
          if fkOrientedLoopVerticalFlux R.medialTorus arrows = -2 then
            fkRectOrientedLoopWeight R lam omega arrows
          else 0 := by
  classical
  let pairing := fkRectConfigurationToMedialPairing R omega
  let S := fkMedialVerticallyWindingComponents pairing
  let down := fkMedialDownwardVerticalMode pairing
  let f := fkRectComponentModeWeight lam pairing
  let K := fkRectChargeOneModeCost lam
  have hf : forall C b, 0 <= f C b := by
    intro C b
    unfold f fkRectComponentModeWeight
    split <;> positivity
  have hlocal : forall C, C ∈ S ->
      f C false + f C true <= K * f C (down C) := by
    intro C hC
    exact componentModeWeight_sum_le_cost_mul R lam hlam pairing down C
  have hall := sum_boolMode_product_le_pow_mul_forced S down f K hf hlocal
  have hcard : S.card <= 2 :=
    card_fkMedialVerticallyWindingComponents_le_two_of_half_eq_one
      pairing hU
  have hK : 1 <= K := fkRectChargeOneModeCost_one_le lam
  have hpow : K ^ S.card <= K ^ 2 := pow_le_pow_right₀ hK hcard
  have hforced0 : 0 <= forcedBoolModeSum S down f := by
    unfold forcedBoolModeSum
    apply Finset.sum_nonneg
    intro mode hmode
    split
    · apply Finset.prod_nonneg
      intro C hC
      exact hf C (mode C)
    · exact le_rfl
  have hforced := forcedDownwardModeSum_le_chargeOneFiber R lam omega hU
  calc
    (∑ arrows : SixVertexArrows R.medialTorus,
        fkRectOrientedLoopWeight R lam omega arrows) =
        ∑ mode : (FKMedialLoop R.medialTorus pairing -> Bool),
          ∏ C, f C (mode C) := by
      change (∑ arrows : SixVertexArrows R.medialTorus,
        fkOrientedLoopPairingWeight lam pairing arrows) = _
      rw [FKMedialTurningFiber.sum_orientedLoopWeight_eq_sum_modes]
      apply Finset.sum_congr rfl
      intro mode hmode
      exact FKMedialTurningFiber.orientedLoopWeight_arrowsOfMode
        lam pairing mode
    _ <= K ^ S.card * forcedBoolModeSum S down f := hall
    _ <= K ^ 2 * forcedBoolModeSum S down f :=
      mul_le_mul_of_nonneg_right hpow hforced0
    _ <= K ^ 2 *
        ∑ arrows : SixVertexArrows R.medialTorus,
          if fkOrientedLoopVerticalFlux R.medialTorus arrows = -2 then
            fkRectOrientedLoopWeight R lam omega arrows
          else 0 :=
      mul_le_mul_of_nonneg_left hforced (by positivity)


theorem fkRectAllTilt_le_modeCost_sq_mul_chargeOneTilt
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (lam : Real) (hlam : 0 <= lam) (omega : R.Configuration)
    (hU : fkRectUnorientedVerticalWindingNumber R omega = 1) :
    fkRectAllOrientedLoopTilt R q lam omega <=
      fkRectChargeOneModeCost lam ^ 2 *
        fkRectFixedChargeTilt R q lam 1
          (one_le_fkRectMedial_halfWidth R) omega := by
  rw [fkRectFixedChargeTilt_eq_verticalFluxTilt]
  unfold fkRectAllOrientedLoopTilt fkRectVerticalFluxTilt
  have hraw := allOrientedLoopWeight_le_modeCost_sq_mul_chargeOneFiber
    R lam hlam omega hU
  have hw := (fkRectCriticalReducedWeight_pos R hq omega).le
  norm_num only [Int.cast_one, mul_one, Int.reduceNeg] at ⊢
  calc
    _ <= (fkRectChargeOneModeCost lam ^ 2 *
        ∑ arrows : SixVertexArrows R.medialTorus,
          if fkOrientedLoopVerticalFlux R.medialTorus arrows = -2 then
            fkRectOrientedLoopWeight R lam omega arrows
          else 0) / fkRectCriticalReducedWeight R q omega :=
      div_le_div_of_nonneg_right hraw hw
    _ = _ := by ring



theorem windingOneAllTiltExpectation_le_modeCost_sq_mul_chargeOneExpectation
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        (if fkRectUnorientedVerticalWindingNumber R omega = 1 then
          fkRectAllOrientedLoopTilt R q lam omega
        else 0)) <=
      fkRectChargeOneModeCost lam ^ 2 *
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega *
            fkRectFixedChargeTilt R q lam 1
              (one_le_fkRectMedial_halfWidth R) omega := by
  dsimp only
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
  have hlam : 0 <= lam :=
    (sixVertexAntiferroelectricLambda_fkQgt4_pos hq).le
  let K := fkRectChargeOneModeCost lam
  have hq0 : 0 < q := by linarith
  have htilt0 (omega : R.Configuration) :
      0 <= fkRectFixedChargeTilt R q lam 1
        (one_le_fkRectMedial_halfWidth R) omega := by
    rw [fkRectFixedChargeTilt_eq_verticalFluxTilt]
    unfold fkRectVerticalFluxTilt
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro arrows harrows
      split
      · exact fkOrientedLoopPairingWeight_nonneg lam
          (fkRectConfigurationToMedialPairing R omega) arrows
      · exact le_rfl
    · exact (fkRectCriticalReducedWeight_pos R hq0 omega).le
  calc
    _ <= ∑ omega : R.Configuration,
        K ^ 2 *
          (fkRectCriticalRandomClusterProb R q omega *
            fkRectFixedChargeTilt R q lam 1
              (one_le_fkRectMedial_halfWidth R) omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      by_cases hU : fkRectUnorientedVerticalWindingNumber R omega = 1
      · rw [if_pos hU]
        have h := mul_le_mul_of_nonneg_left
          (fkRectAllTilt_le_modeCost_sq_mul_chargeOneTilt
            R hq0 lam hlam omega hU)
          (fkRectCriticalRandomClusterProb_nonneg R hq0 omega)
        simpa [lam, K, mul_assoc, mul_left_comm, mul_comm] using h
      · rw [if_neg hU]
        simpa using mul_nonneg (sq_nonneg K)
          (mul_nonneg
            (fkRectCriticalRandomClusterProb_nonneg R hq0 omega)
            (htilt0 omega))
    _ = K ^ 2 * ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectFixedChargeTilt R q lam 1
            (one_le_fkRectMedial_halfWidth R) omega := by
      rw [Finset.mul_sum]
    _ = _ := rfl


theorem windingOneAllTiltExpectation_le_modeCost_sq_mul_chargeOneRatio
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        (if fkRectUnorientedVerticalWindingNumber R omega = 1 then
          fkRectAllOrientedLoopTilt R q lam omega
        else 0)) <=
      fkRectChargeOneModeCost lam ^ 2 *
        (sixVertexTorusFixedChargePartitionSum R.medialTorus 1
            (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
          fkRectCriticalReducedZ R q) := by
  dsimp only
  calc
    _ <= fkRectChargeOneModeCost
          (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2 *
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega *
            fkRectFixedChargeTilt R q
              (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
              1 (one_le_fkRectMedial_halfWidth R) omega :=
      windingOneAllTiltExpectation_le_modeCost_sq_mul_chargeOneExpectation
        R hq
    _ = _ := by
      rw [sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
        R hq 1 (one_le_fkRectMedial_halfWidth R)]

end

end StatMech.FrontierD
