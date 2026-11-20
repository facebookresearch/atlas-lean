/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierD.FKRectTorusAllChargeReduction
import Code.FrontierD.FKMedialLoopVerticalWinding
import Code.FrontierD.FKMedialLoopTurningFiber
import Code.FrontierD.FKRectMedialLoopTurnClassification
import Code.FrontierD.FKRectEulerDefectClassification

namespace StatMech.FrontierD

noncomputable section



def fkRectUnorientedVerticalWindingTotal
    (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  fkMedialUnorientedVerticalWindingTotal
    (fkRectConfigurationToMedialPairing R omega)


def fkRectUnorientedVerticalWindingNumber
    (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  fkRectUnorientedVerticalWindingTotal R omega / 2





theorem fkRectFixedChargeTilt_pos_of_windingNumber_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (lam : Real)
    (omega : R.Configuration) (r : Nat)
    (hr : r ≤ R.medialTorus.width / 2)
    (hU : fkRectUnorientedVerticalWindingNumber R omega = r) :
    0 < fkRectFixedChargeTilt R q lam r hr omega := by
  obtain ⟨arrows, hweight, hflux⟩ :=
    exists_positive_weight_verticalFlux_eq_neg_two_mul_half lam
      (fkRectConfigurationToMedialPairing R omega)
  have hU' :
      ((fkMedialUnorientedVerticalWindingTotal
          (fkRectConfigurationToMedialPairing R omega) / 2 : Nat) : Int) =
        (r : Int) := by
    exact_mod_cast hU
  have hflux' : fkOrientedLoopVerticalFlux R.medialTorus arrows =
      -(2 * (r : Int)) := by
    rw [hU'] at hflux
    exact hflux
  rw [fkRectFixedChargeTilt_eq_verticalFluxTilt]
  unfold fkRectVerticalFluxTilt
  apply div_pos
  · apply Finset.sum_pos'
    · intro a ha
      split
      · exact fkOrientedLoopPairingWeight_nonneg lam
          (fkRectConfigurationToMedialPairing R omega) a
      · norm_num
    · refine ⟨arrows, Finset.mem_univ _, ?_⟩
      rw [if_pos hflux']
      exact hweight
  · exact fkRectCriticalReducedWeight_pos R hq omega



theorem fkRectUnorientedVerticalWindingNumber_ge_of_weight_ne_zero_of_flux
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration)
    (arrows : SixVertexArrows R.medialTorus) (r : Nat)
    (hweight : fkRectOrientedLoopWeight R lam omega arrows ≠ 0)
    (hflux : fkOrientedLoopVerticalFlux R.medialTorus arrows =
      -(2 * (r : Int))) :
    r ≤ fkRectUnorientedVerticalWindingNumber R omega := by
  have hcompat : ∀ v,
      fkLoopPairingCompatible
        (fkRectConfigurationToMedialPairing R omega v) arrows v := by
    exact (fkOrientedLoopPairingWeight_ne_zero_iff_compatible
      lam (fkRectConfigurationToMedialPairing R omega) arrows).1 hweight
  exact le_half_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul
    (fkRectConfigurationToMedialPairing R omega) arrows hcompat r hflux


theorem fkRectUnorientedVerticalWindingNumber_ge_of_fixedCharge
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration)
    (arrows : SixVertexArrows R.medialTorus)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2)
    (hweight : fkRectOrientedLoopWeight R lam omega arrows ≠ 0)
    (hsector : sixVertexUpCount
        (svTorusVerticalRows R.medialTorus arrows
          (svFinLast R.medialTorus.height_pos)) =
      R.medialTorus.width / 2 - r) :
    r ≤ fkRectUnorientedVerticalWindingNumber R omega := by
  apply fkRectUnorientedVerticalWindingNumber_ge_of_weight_ne_zero_of_flux
    R lam omega arrows r hweight
  exact fkOrientedLoopVerticalFlux_eq_neg_two_mul_of_fixedCharge
    R.medialTorus arrows r hr hsector




theorem fkRectVerticalFluxSummand_ne_zero_imp_windingNumber_ge
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration)
    (arrows : SixVertexArrows R.medialTorus) (r : Nat)
    (hterm : (if fkOrientedLoopVerticalFlux R.medialTorus arrows =
          -(2 * (r : Int)) then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0) ≠ 0) :
    r ≤ fkRectUnorientedVerticalWindingNumber R omega := by
  by_cases hflux : fkOrientedLoopVerticalFlux R.medialTorus arrows =
      -(2 * (r : Int))
  · apply fkRectUnorientedVerticalWindingNumber_ge_of_weight_ne_zero_of_flux
      R lam omega arrows r
    · simpa [hflux] using hterm
    · exact hflux
  · simp [hflux] at hterm



theorem fkRectFixedChargeSummand_le_windingRestrictedSummand
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration)
    (arrows : SixVertexArrows R.medialTorus)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    (if sixVertexUpCount
          (svTorusVerticalRows R.medialTorus arrows
            (svFinLast R.medialTorus.height_pos)) =
          R.medialTorus.width / 2 - r then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0) ≤
      if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0 := by
  by_cases hsector : sixVertexUpCount
      (svTorusVerticalRows R.medialTorus arrows
        (svFinLast R.medialTorus.height_pos)) =
      R.medialTorus.width / 2 - r
  · rw [if_pos hsector]
    by_cases hweight : fkRectOrientedLoopWeight R lam omega arrows = 0
    · simp [hweight]
    · have hU := fkRectUnorientedVerticalWindingNumber_ge_of_fixedCharge
        R lam omega arrows r hr hweight hsector
      rw [if_pos hU]
  · rw [if_neg hsector]
    by_cases hU : r ≤ fkRectUnorientedVerticalWindingNumber R omega
    · rw [if_pos hU]
      exact fkOrientedLoopPairingWeight_nonneg lam
        (fkRectConfigurationToMedialPairing R omega) arrows
    · rw [if_neg hU]




theorem fkRectOrientedLoopFixedChargePartitionSum_le_windingRestricted
    (R : FKRectTorus) (lam : Real)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    fkRectOrientedLoopSectorPartitionSum R
        (fkRectFixedChargeSector R r hr) lam ≤
      ∑ omega : R.Configuration,
        if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          ∑ arrows : SixVertexArrows R.medialTorus,
            fkRectOrientedLoopWeight R lam omega arrows
        else 0 := by
  unfold fkRectOrientedLoopSectorPartitionSum fkRectFixedChargeSector
  apply Finset.sum_le_sum
  intro omega homega
  calc
    (∑ arrows : SixVertexArrows R.medialTorus,
        if sixVertexUpCount
            (svTorusVerticalRows R.medialTorus arrows
              (svFinLast R.medialTorus.height_pos)) =
            R.medialTorus.width / 2 - r then
          fkRectOrientedLoopWeight R lam omega arrows
        else 0) ≤
        ∑ arrows : SixVertexArrows R.medialTorus,
          if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectOrientedLoopWeight R lam omega arrows
          else 0 := by
      apply Finset.sum_le_sum
      intro arrows harrows
      exact fkRectFixedChargeSummand_le_windingRestrictedSummand
        R lam omega arrows r hr
    _ = if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          ∑ arrows : SixVertexArrows R.medialTorus,
            fkRectOrientedLoopWeight R lam omega arrows
        else 0 := by
      split <;> simp_all



def fkRectAllOrientedLoopTilt (R : FKRectTorus) (q lam : Real)
    (omega : R.Configuration) : Real :=
  (∑ arrows : SixVertexArrows R.medialTorus,
      fkRectOrientedLoopWeight R lam omega arrows) /
    fkRectCriticalReducedWeight R q omega




def fkRectZeroTurnLoopCount (R : FKRectTorus)
    (omega : R.Configuration) : Nat :=
  (Finset.univ.filter fun C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega) =>
    FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C = 0).card


def fkRectNonzeroTurnLoopCount (R : FKRectTorus)
    (omega : R.Configuration) : Nat :=
  (Finset.univ.filter fun C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega) =>
    FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C ≠ 0).card

theorem fkRectZeroTurnLoopCount_add_nonzeroTurnLoopCount
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectZeroTurnLoopCount R omega +
        fkRectNonzeroTurnLoopCount R omega =
      fkRectMedialLoopCount R omega := by
  classical
  unfold fkRectZeroTurnLoopCount fkRectNonzeroTurnLoopCount
    fkRectMedialLoopCount fkMedialLoopCount
  rw [Nat.card_eq_fintype_card]
  simpa using (Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))))
    (p := fun C => FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C = 0))



theorem sum_fkRectOrientedLoopWeight_eq_turningProduct
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration) :
    (∑ arrows : SixVertexArrows R.medialTorus,
        fkRectOrientedLoopWeight R lam omega arrows) =
      ∏ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        (Real.exp ((lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C) +
          Real.exp (-(lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C)) := by
  exact FKMedialTurningFiber.sum_orientedLoopWeight_eq_turningProduct
    lam (fkRectConfigurationToMedialPairing R omega)

theorem fkRectTurningProduct_eq_zero_nonzeroTurnPowers
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration) :
    (∏ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        (Real.exp ((lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C) +
          Real.exp (-(lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C))) =
      2 ^ fkRectZeroTurnLoopCount R omega *
        (Real.exp lam + Real.exp (-lam)) ^
          fkRectNonzeroTurnLoopCount R omega := by
  classical
  unfold fkRectZeroTurnLoopCount fkRectNonzeroTurnLoopCount
  rw [← Finset.prod_filter_mul_prod_filter_not
    (s := (Finset.univ : Finset (FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))))
    (p := fun C => FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C = 0)]
  congr 1
  · apply Finset.prod_eq_pow_card
    intro C hC
    apply FKMedialTurningFiber.orientationFactor_eq_two_of_turn_eq_zero
    exact (Finset.mem_filter.mp hC).2
  · apply Finset.prod_eq_pow_card
    intro C hC
    have hne := (Finset.mem_filter.mp hC).2
    have hclass := fkRectCanonicalComponentTurn_classification R
      (fkRectConfigurationToMedialPairing R omega) C
    apply FKMedialTurningFiber.orientationFactor_eq_exp_add_exp_neg_of_turn_eq_four_or_neg_four
    rcases hclass with hzero | hfour | hnegfour
    · exact (hne hzero).elim
    · exact Or.inl hfour
    · exact Or.inr hnegfour

theorem sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration) :
    (∑ arrows : SixVertexArrows R.medialTorus,
        fkRectOrientedLoopWeight R lam omega arrows) =
      2 ^ fkRectZeroTurnLoopCount R omega *
        (Real.exp lam + Real.exp (-lam)) ^
          fkRectNonzeroTurnLoopCount R omega := by
  rw [sum_fkRectOrientedLoopWeight_eq_turningProduct,
    fkRectTurningProduct_eq_zero_nonzeroTurnPowers]



theorem fkRectAllOrientedLoopTilt_eq_turningProduct
    (R : FKRectTorus) (q lam : Real) (omega : R.Configuration) :
    fkRectAllOrientedLoopTilt R q lam omega =
      (∏ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        (Real.exp ((lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C) +
          Real.exp (-(lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C))) /
        fkRectCriticalReducedWeight R q omega := by
  unfold fkRectAllOrientedLoopTilt
  rw [sum_fkRectOrientedLoopWeight_eq_turningProduct]





theorem fkRectAllOrientedLoopTilt_eq_turningProduct_div_loopDefect
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (lam : Real)
    (omega : R.Configuration) :
    fkRectAllOrientedLoopTilt R q lam omega =
      (∏ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        (Real.exp ((lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C) +
          Real.exp (-(lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C))) /
        (Real.sqrt q ^ (R.width * R.height : Nat) *
          Real.sqrt q ^ fkRectMedialLoopCount R omega *
            Real.sqrt q ^ fkRectEulerHomologyDefect R omega) := by
  rw [fkRectAllOrientedLoopTilt_eq_turningProduct]
  rw [fkRectCriticalReducedWeight_eq_loop_defect R hq]

theorem sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers_fkQgt4
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ arrows : SixVertexArrows R.medialTorus,
        fkRectOrientedLoopWeight R lam omega arrows) =
      2 ^ fkRectZeroTurnLoopCount R omega *
        Real.sqrt q ^ fkRectNonzeroTurnLoopCount R omega := by
  dsimp only
  rw [sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers,
    exp_add_exp_neg_sixVertexLambda_fkQgt4 hq]





theorem fkRectAllOrientedLoopTilt_eq_zeroTurnLoopCount_fkQgt4
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    fkRectAllOrientedLoopTilt R q lam omega =
      (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
        (Real.sqrt q ^ (R.width * R.height : Nat) *
          Real.sqrt q ^ fkRectEulerHomologyDefect R omega) := by
  dsimp only
  rw [fkRectAllOrientedLoopTilt_eq_turningProduct_div_loopDefect
    R (by linarith)]
  rw [fkRectTurningProduct_eq_zero_nonzeroTurnPowers,
    exp_add_exp_neg_sixVertexLambda_fkQgt4 hq]
  rw [← fkRectZeroTurnLoopCount_add_nonzeroTurnLoopCount R omega,
    pow_add, div_pow]
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  field_simp [hs]



def fkRectZeroTurnEulerResidual (R : FKRectTorus) (q : Real)
    (omega : R.Configuration) : Real :=
  (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
    Real.sqrt q ^ fkRectEulerHomologyDefect R omega

theorem fkRectZeroTurnEulerResidual_nonneg
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    0 ≤ fkRectZeroTurnEulerResidual R q omega := by
  unfold fkRectZeroTurnEulerResidual
  positivity

theorem fkRectZeroTurnEulerResidual_le_one
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    fkRectZeroTurnEulerResidual R q omega ≤ 1 := by
  have hq0 : 0 ≤ q := by linarith
  have hspos : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  have hs2 : 2 ≤ Real.sqrt q := by
    nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
  have hb0 : 0 ≤ 2 / Real.sqrt q := by positivity
  have hb1 : 2 / Real.sqrt q ≤ 1 :=
    (div_le_one hspos).2 hs2
  have hpow : (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega ≤ 1 :=
    pow_le_one₀ hb0 hb1
  have hdef := fkRectEulerHomologyDefect_classified R
    (fkRectOpenEdges R omega)
  rw [fkRectConfigurationOfEdges_openEdges] at hdef
  rcases hdef with hzero | htwo
  · simpa [fkRectZeroTurnEulerResidual, hzero] using hpow
  · unfold fkRectZeroTurnEulerResidual
    rw [htwo]
    have hden : Real.sqrt q ^ (2 : Int) = q := by
      simpa only [zpow_ofNat] using Real.sq_sqrt hq0
    rw [hden]
    exact (div_le_one (by linarith)).2 (hpow.trans (by linarith))



def fkRectCriticalWindingTailMass (R : FKRectTorus) (q : Real)
    (r : Nat) : Real :=
  ∑ omega : R.Configuration,
    if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
      fkRectCriticalRandomClusterProb R q omega
    else 0

theorem fkRectCriticalWindingTailMass_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (r : Nat) :
    0 ≤ fkRectCriticalWindingTailMass R q r := by
  unfold fkRectCriticalWindingTailMass
  apply Finset.sum_nonneg
  intro omega homega
  split
  · exact fkRectCriticalRandomClusterProb_nonneg R hq omega
  · exact le_rfl

theorem fkRectCriticalWindingTailMass_le_one
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (r : Nat) :
    fkRectCriticalWindingTailMass R q r ≤ 1 := by
  unfold fkRectCriticalWindingTailMass
  calc
    (∑ omega : R.Configuration,
      if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
        fkRectCriticalRandomClusterProb R q omega
      else 0) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega := by
      apply Finset.sum_le_sum
      intro omega homega
      split
      · exact le_rfl
      · exact fkRectCriticalRandomClusterProb_nonneg R hq omega
    _ = 1 := sum_fkRectCriticalRandomClusterProb R hq

theorem fkRectAllOrientedLoopTilt_eq_residual_div_area_fkQgt4
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    fkRectAllOrientedLoopTilt R q lam omega =
      fkRectZeroTurnEulerResidual R q omega /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  dsimp only
  rw [fkRectAllOrientedLoopTilt_eq_zeroTurnLoopCount_fkQgt4 R hq]
  unfold fkRectZeroTurnEulerResidual
  ring




theorem sum_rcProb_mul_windingRestrictedAllOrientedLoopTilt
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (lam : Real) (r : Nat) :
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          fkRectAllOrientedLoopTilt R q lam omega
        else 0)) =
      (∑ omega : R.Configuration,
        if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          ∑ arrows : SixVertexArrows R.medialTorus,
            fkRectOrientedLoopWeight R lam omega arrows
        else 0) / fkRectCriticalReducedZ R q := by
  calc
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          fkRectAllOrientedLoopTilt R q lam omega
        else 0)) =
        ∑ omega : R.Configuration,
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            ∑ arrows : SixVertexArrows R.medialTorus,
              fkRectOrientedLoopWeight R lam omega arrows
          else 0) / fkRectCriticalReducedZ R q := by
      apply Finset.sum_congr rfl
      intro omega homega
      by_cases hU : r ≤ fkRectUnorientedVerticalWindingNumber R omega
      · rw [if_pos hU, if_pos hU]
        unfold fkRectCriticalRandomClusterProb fkRectAllOrientedLoopTilt
        have hw := (fkRectCriticalReducedWeight_pos R hq omega).ne'
        have hz := (fkRectCriticalReducedZ_pos R hq).ne'
        field_simp
      · simp [hU]
    _ = _ := by rw [Finset.sum_div]





theorem sum_rcProb_mul_fixedChargeTilt_le_windingRestrictedAllTilt
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectFixedChargeTilt R q lam r hr omega) ≤
      ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectAllOrientedLoopTilt R q lam omega
          else 0) := by
  dsimp only
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
  let restricted : Real :=
    ∑ omega : R.Configuration,
      if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
        ∑ arrows : SixVertexArrows R.medialTorus,
          fkRectOrientedLoopWeight R lam omega arrows
      else 0
  have hraw : fkRectOrientedLoopSectorPartitionSum R
      (fkRectFixedChargeSector R r hr) lam ≤ restricted := by
    exact fkRectOrientedLoopFixedChargePartitionSum_le_windingRestricted
      R lam r hr
  have hsector : sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
        (fkQgt4SixVertexWeight q) =
      fkRectOrientedLoopSectorPartitionSum R
        (fkRectFixedChargeSector R r hr) lam := by
    rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
    rw [fkRectOrientedLoopSectorPartitionSum_eq_sectorTrace]
    rw [exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4 hq]
    simp [fkRectFixedChargeSector]
    rfl
  rw [sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
    R hq r hr]
  rw [sum_rcProb_mul_windingRestrictedAllOrientedLoopTilt
    R (by linarith) lam r]
  rw [hsector]
  exact div_le_div_of_nonneg_right hraw
    (le_of_lt (fkRectCriticalReducedZ_pos R (by linarith)))




theorem sum_rcProb_mul_windingRestrictedAllTilt_eq_residual_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q) (r : Nat) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          fkRectAllOrientedLoopTilt R q lam omega
        else 0)) =
      (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectZeroTurnEulerResidual R q omega
          else 0)) /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  dsimp only
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hU : r ≤ fkRectUnorientedVerticalWindingNumber R omega
  · rw [if_pos hU, if_pos hU,
      fkRectAllOrientedLoopTilt_eq_residual_div_area_fkQgt4 R hq]
    ring
  · simp [hU]

theorem sum_rcProb_mul_windingResidual_le_windingTailMass
    (R : FKRectTorus) {q : Real} (hq : 4 < q) (r : Nat) :
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          fkRectZeroTurnEulerResidual R q omega
        else 0)) ≤
      fkRectCriticalWindingTailMass R q r := by
  unfold fkRectCriticalWindingTailMass
  apply Finset.sum_le_sum
  intro omega homega
  by_cases hU : r ≤ fkRectUnorientedVerticalWindingNumber R omega
  · rw [if_pos hU, if_pos hU]
    exact mul_le_of_le_one_right
      (fkRectCriticalRandomClusterProb_nonneg R (by linarith) omega)
      (fkRectZeroTurnEulerResidual_le_one R hq omega)
  · simp [hU]




theorem sum_rcProb_mul_fixedChargeTilt_le_residual_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectFixedChargeTilt R q lam r hr omega) ≤
      (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectZeroTurnEulerResidual R q omega
          else 0)) /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  dsimp only
  calc
    _ ≤ ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectAllOrientedLoopTilt R q
              (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
              omega
          else 0) :=
      sum_rcProb_mul_fixedChargeTilt_le_windingRestrictedAllTilt
        R hq r hr
    _ = _ :=
      sum_rcProb_mul_windingRestrictedAllTilt_eq_residual_div_area
        R hq r

theorem sixVertexFixedCharge_div_fkZ_le_residual_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectZeroTurnEulerResidual R q omega
          else 0)) /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  rw [← sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
    R hq r hr]
  exact sum_rcProb_mul_fixedChargeTilt_le_residual_div_area R hq r hr




theorem sixVertexFixedCharge_div_fkZ_le_windingTail_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      fkRectCriticalWindingTailMass R q r /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  calc
    _ ≤ (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectZeroTurnEulerResidual R q omega
          else 0)) /
        Real.sqrt q ^ (R.width * R.height : Nat) :=
      sixVertexFixedCharge_div_fkZ_le_residual_div_area R hq r hr
    _ ≤ _ := div_le_div_of_nonneg_right
      (sum_rcProb_mul_windingResidual_le_windingTailMass R hq r)
      (by positivity)




theorem sixVertexFixedCharge_div_fkZ_le_invSqrtQ_pow_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      (1 / Real.sqrt q) ^ (R.width * R.height : Nat) := by
  calc
    _ ≤ fkRectCriticalWindingTailMass R q r /
        Real.sqrt q ^ (R.width * R.height : Nat) :=
      sixVertexFixedCharge_div_fkZ_le_windingTail_div_area R hq r hr
    _ ≤ 1 / Real.sqrt q ^ (R.width * R.height : Nat) :=
      div_le_div_of_nonneg_right
        (fkRectCriticalWindingTailMass_le_one R (by linarith) r)
        (by positivity)
    _ = _ := by rw [one_div_pow]

theorem sixVertexFixedCharge_div_fkZ_pos
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    0 < sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q := by
  apply div_pos
  · rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
    have hc : 0 < fkQgt4SixVertexWeight q := by
      linarith [two_lt_fkQgt4SixVertexWeight hq]
    exact sixVertexSector_trace_pow_pos
      (N := R.medialTorus.width)
      (n := R.medialTorus.width / 2 - r)
      (c := fkQgt4SixVertexWeight q)
      ((Nat.sub_le _ _).trans
        (Nat.div_le_self R.medialTorus.width 2))
      hc R.medialTorus.height
  · exact fkRectCriticalReducedZ_pos R (by linarith)




def fkRectBalancedSectorNormalization (R : FKRectTorus) (q : Real) : Real :=
  Real.sqrt q ^ (R.width * R.height : Nat) *
    (sixVertexTorusFixedChargePartitionSum R.medialTorus 0
        (Nat.zero_le _) (fkQgt4SixVertexWeight q) /
      fkRectCriticalReducedZ R q)

theorem fkRectBalancedSectorNormalization_pos
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    0 < fkRectBalancedSectorNormalization R q := by
  unfold fkRectBalancedSectorNormalization
  exact mul_pos (pow_pos (Real.sqrt_pos.2 (by linarith)) _)
    (sixVertexFixedCharge_div_fkZ_pos R hq 0 (Nat.zero_le _))

theorem fkRectBalancedSectorNormalization_eq_chargeZeroExpectation
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    fkRectBalancedSectorNormalization R q =
      Real.sqrt q ^ (R.width * R.height : Nat) *
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega *
            fkRectFixedChargeTilt R q lam 0 (Nat.zero_le _) omega := by
  dsimp only
  unfold fkRectBalancedSectorNormalization
  rw [sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
    R hq 0 (Nat.zero_le _)]




theorem sixVertexFixedCharge_div_chargeZero_eq_areaNormalizedRatio
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        sixVertexTorusFixedChargePartitionSum R.medialTorus 0
          (Nat.zero_le _) (fkQgt4SixVertexWeight q) =
      (Real.sqrt q ^ (R.width * R.height : Nat) *
          (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
              (fkQgt4SixVertexWeight q) /
            fkRectCriticalReducedZ R q)) /
        fkRectBalancedSectorNormalization R q := by
  unfold fkRectBalancedSectorNormalization
  have hZ : fkRectCriticalReducedZ R q ≠ 0 :=
    (fkRectCriticalReducedZ_pos R (by linarith)).ne'
  have hZ0 : sixVertexTorusFixedChargePartitionSum R.medialTorus 0
      (Nat.zero_le _) (fkQgt4SixVertexWeight q) ≠ 0 := by
    have h := sixVertexFixedCharge_div_fkZ_pos R hq 0 (Nat.zero_le _)
    exact fun hz => by simp [hz] at h
  have hA : Real.sqrt q ^ (R.width * R.height : Nat) ≠ 0 :=
    pow_ne_zero _ (Real.sqrt_pos.2 (by linarith)).ne'
  field_simp [hZ, hZ0, hA]



theorem sixVertexFixedCharge_div_chargeZero_le_windingTail_div_balanced
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        sixVertexTorusFixedChargePartitionSum R.medialTorus 0
          (Nat.zero_le _) (fkQgt4SixVertexWeight q) ≤
      fkRectCriticalWindingTailMass R q r /
        fkRectBalancedSectorNormalization R q := by
  rw [sixVertexFixedCharge_div_chargeZero_eq_areaNormalizedRatio R hq r hr]
  apply div_le_div_of_nonneg_right _
    (fkRectBalancedSectorNormalization_pos R hq).le
  have hfinite := sixVertexFixedCharge_div_fkZ_le_windingTail_div_area
    R hq r hr
  have hA : 0 ≤ Real.sqrt q ^ (R.width * R.height : Nat) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hfinite hA
  have hAne : Real.sqrt q ^ (R.width * R.height : Nat) ≠ 0 := by
    positivity
  field_simp [hAne] at hmul
  simpa only [mul_div_assoc] using hmul


theorem log_sqrtQ_le_fixedCharge_negLogRate_per_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    Real.log (Real.sqrt q) ≤
      -Real.log
          (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
              (fkQgt4SixVertexWeight q) /
            fkRectCriticalReducedZ R q) /
        (R.width * R.height : Nat) := by
  let x := sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
      (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q
  let A := R.width * R.height
  have hx : 0 < x := sixVertexFixedCharge_div_fkZ_pos R hq r hr
  have hxy : x ≤ (1 / Real.sqrt q) ^ A :=
    sixVertexFixedCharge_div_fkZ_le_invSqrtQ_pow_area R hq r hr
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hlog := Real.log_le_log hx hxy
  have hylog : Real.log ((1 / Real.sqrt q) ^ A) =
      -(A : Real) * Real.log (Real.sqrt q) := by
    rw [Real.log_pow, Real.log_div one_ne_zero hs, Real.log_one]
    ring
  rw [hylog] at hlog
  have hApos : (0 : Real) < A := by
    exact_mod_cast Nat.mul_pos R.width_pos R.height_pos
  rw [le_div_iff₀ hApos]
  dsimp [x, A] at hlog ⊢
  linarith

theorem sixVertexChargeOne_div_fkZ_le_residual_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus 1
          (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if 1 ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectZeroTurnEulerResidual R q omega
          else 0)) /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  exact sixVertexFixedCharge_div_fkZ_le_residual_div_area R hq 1
    (one_le_fkRectMedial_halfWidth R)

theorem sixVertexChargeOne_div_fkZ_le_windingTail_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus 1
          (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      fkRectCriticalWindingTailMass R q 1 /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  exact sixVertexFixedCharge_div_fkZ_le_windingTail_div_area R hq 1
    (one_le_fkRectMedial_halfWidth R)

theorem sixVertexChargeOne_div_fkZ_le_invSqrtQ_pow_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus 1
          (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      (1 / Real.sqrt q) ^ (R.width * R.height : Nat) := by
  exact sixVertexFixedCharge_div_fkZ_le_invSqrtQ_pow_area R hq 1
    (one_le_fkRectMedial_halfWidth R)

end

end StatMech.FrontierD
