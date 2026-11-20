/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusRandomCluster
import Code.FrontierD.FKQgt4ParameterBridge

open scoped BigOperators
open Matrix

namespace StatMech.FrontierD

noncomputable section



def fkRectOrientedLoopWeight (R : FKRectTorus) (lam : Real)
    (omega : R.Configuration) (arrows : SixVertexArrows R.medialTorus) : Real :=
  fkOrientedLoopPairingWeight lam
    (fkRectConfigurationToMedialPairing R omega) arrows



def fkRectOrientedLoopPartitionSum (R : FKRectTorus) (lam : Real) : Real :=
  ∑ omega : R.Configuration,
    ∑ arrows : SixVertexArrows R.medialTorus,
      fkRectOrientedLoopWeight R lam omega arrows

theorem fkRectOrientedLoopPartitionSum_eq_generic
    (R : FKRectTorus) (lam : Real) :
    fkRectOrientedLoopPartitionSum R lam =
      fkOrientedLoopPartitionSum R.medialTorus lam := by
  unfold fkRectOrientedLoopPartitionSum fkOrientedLoopPartitionSum
    fkRectOrientedLoopWeight
  rw [Equiv.sum_comp (fkRectConfigurationToMedialPairing R)
    (fun pairing => ∑ arrows : SixVertexArrows R.medialTorus,
      fkOrientedLoopPairingWeight lam pairing arrows)]
  rw [Finset.sum_comm]

theorem fkRectOrientedLoopPartitionSum_eq_sixVertex
    (R : FKRectTorus) (lam : Real) :
    fkRectOrientedLoopPartitionSum R lam =
      sixVertexTorusArrowPartitionSum R.medialTorus
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) := by
  rw [fkRectOrientedLoopPartitionSum_eq_generic]
  exact fkOrientedLoopPartitionSum_eq_sixVertexTorusArrowPartitionSum _ _


def fkRectOrientedLoopSectorPartitionSum
    (R : FKRectTorus) (n : Fin (R.medialTorus.width + 1))
    (lam : Real) : Real :=
  ∑ omega : R.Configuration,
    ∑ arrows : SixVertexArrows R.medialTorus,
      if sixVertexUpCount
          (svTorusVerticalRows R.medialTorus arrows
            (svFinLast R.medialTorus.height_pos)) = n.val then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0

theorem fkRectOrientedLoopSectorPartitionSum_eq_generic
    (R : FKRectTorus) (n : Fin (R.medialTorus.width + 1))
    (lam : Real) :
    fkRectOrientedLoopSectorPartitionSum R n lam =
      fkOrientedLoopSectorPartitionSum R.medialTorus n lam := by
  unfold fkRectOrientedLoopSectorPartitionSum
    fkOrientedLoopSectorPartitionSum fkRectOrientedLoopWeight
  rw [Equiv.sum_comp (fkRectConfigurationToMedialPairing R)
    (fun pairing => ∑ arrows : SixVertexArrows R.medialTorus,
      if sixVertexUpCount
          (svTorusVerticalRows R.medialTorus arrows
            (svFinLast R.medialTorus.height_pos)) = n.val then
        fkOrientedLoopPairingWeight lam pairing arrows
      else 0)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro arrows harrows
  by_cases hn : sixVertexUpCount
      (svTorusVerticalRows R.medialTorus arrows
        (svFinLast R.medialTorus.height_pos)) = n.val
  · simp [hn]
  · simp [hn]

theorem fkRectOrientedLoopSectorPartitionSum_eq_sectorTrace
    (R : FKRectTorus) (n : Fin (R.medialTorus.width + 1))
    (lam : Real) :
    fkRectOrientedLoopSectorPartitionSum R n lam =
      Matrix.trace
        (sixVertexSectorTransfer R.medialTorus.width n.val
          (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^
            R.medialTorus.height) := by
  rw [fkRectOrientedLoopSectorPartitionSum_eq_generic,
    fkOrientedLoopSectorPartitionSum_eq_sixVertexSector]
  exact svTorusSectorArrowPartitionSum_eq_sectorTrace _ _ _



theorem exp_add_exp_neg_sixVertexLambda_fkQgt4
    {q : Real} (hq : 4 < q) :
    Real.exp
        (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) +
      Real.exp
        (-sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) =
      Real.sqrt q := by
  have hc := cosh_sixVertexAntiferroelectricLambda_fkQgt4 hq
  rw [Real.cosh_eq] at hc
  linarith



theorem exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4
    {q : Real} (hq : 4 < q) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    Real.exp (lam / 2) + Real.exp (-lam / 2) =
      fkQgt4SixVertexWeight q := by
  dsimp only
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
  have hsum : Real.exp lam + Real.exp (-lam) = Real.sqrt q := by
    exact exp_add_exp_neg_sixVertexLambda_fkQgt4 hq
  have hprod : Real.exp (lam / 2) * Real.exp (-lam / 2) = 1 := by
    rw [<- Real.exp_add]
    rw [<- Real.exp_zero]
    congr 1
    ring
  have hpos : 0 < Real.exp (lam / 2) + Real.exp (-lam / 2) := by positivity
  have ha2 : Real.exp (lam / 2) ^ 2 = Real.exp lam := by
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  have hb2 : Real.exp (-lam / 2) ^ 2 = Real.exp (-lam) := by
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  have hsquare :
      (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^ 2 =
        2 + Real.sqrt q := by
    nlinarith
  have hcSquare := fkQgt4SixVertexWeight_sq hq
  have hcNonneg : 0 <= fkQgt4SixVertexWeight q := by
    unfold fkQgt4SixVertexWeight
    positivity
  dsimp only [lam] at hpos hsquare
  nlinarith



def fkRectSignedChargeTilt (R : FKRectTorus) (q lam : Real)
    (n : Fin (R.medialTorus.width + 1))
    (omega : R.Configuration) : Real :=
  (∑ arrows : SixVertexArrows R.medialTorus,
      if sixVertexUpCount
          (svTorusVerticalRows R.medialTorus arrows
            (svFinLast R.medialTorus.height_pos)) = n.val then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0) /
    fkRectCriticalReducedWeight R q omega





theorem sum_rcProb_mul_fkRectSignedChargeTilt_eq_sectorTrace_div_Z
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (n : Fin (R.medialTorus.width + 1)) (lam : Real) :
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectSignedChargeTilt R q lam n omega) =
      Matrix.trace
          (sixVertexSectorTransfer R.medialTorus.width n.val
            (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^
              R.medialTorus.height) /
        fkRectCriticalReducedZ R q := by
  let fiber : R.Configuration -> Real := fun omega =>
    ∑ arrows : SixVertexArrows R.medialTorus,
      if sixVertexUpCount
          (svTorusVerticalRows R.medialTorus arrows
            (svFinLast R.medialTorus.height_pos)) = n.val then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectSignedChargeTilt R q lam n omega) =
        ∑ omega : R.Configuration,
          fiber omega / fkRectCriticalReducedZ R q := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [fkRectCriticalRandomClusterProb, fkRectSignedChargeTilt]
      dsimp only [fiber]
      have hw := (fkRectCriticalReducedWeight_pos R hq omega).ne'
      have hz := (fkRectCriticalReducedZ_pos R hq).ne'
      field_simp
    _ = (∑ omega : R.Configuration, fiber omega) /
          fkRectCriticalReducedZ R q := by
      rw [Finset.sum_div]
    _ = fkRectOrientedLoopSectorPartitionSum R n lam /
          fkRectCriticalReducedZ R q := by
      rfl
    _ = Matrix.trace
          (sixVertexSectorTransfer R.medialTorus.width n.val
            (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^
              R.medialTorus.height) /
          fkRectCriticalReducedZ R q := by
      rw [fkRectOrientedLoopSectorPartitionSum_eq_sectorTrace]



theorem sum_rcProb_mul_fkRectSignedChargeTilt_eq_canonicalSectorTrace_div_Z
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (n : Fin (R.medialTorus.width + 1)) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectSignedChargeTilt R q lam n omega) =
      Matrix.trace
          (sixVertexSectorTransfer R.medialTorus.width n.val
            (fkQgt4SixVertexWeight q) ^ R.medialTorus.height) /
        fkRectCriticalReducedZ R q := by
  dsimp only
  rw [sum_rcProb_mul_fkRectSignedChargeTilt_eq_sectorTrace_div_Z
    R (by linarith) n]
  rw [exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4 hq]

end

end StatMech.FrontierD
