/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusSignedChargeBridge
import Code.FrontierD.FKMedialLoopTopology

open Matrix

namespace StatMech.FrontierD

noncomputable section


def fkRectFixedChargeSector (R : FKRectTorus) (r : Nat)
    (_hr : r <= R.medialTorus.width / 2) :
    Fin (R.medialTorus.width + 1) :=
  ⟨R.medialTorus.width / 2 - r,
    Nat.lt_succ_of_le
      ((Nat.sub_le _ _).trans
        (Nat.div_le_self R.medialTorus.width 2))⟩



def fkRectFixedChargeTilt (R : FKRectTorus) (q lam : Real)
    (r : Nat) (hr : r <= R.medialTorus.width / 2)
    (omega : R.Configuration) : Real :=
  fkRectSignedChargeTilt R q lam (fkRectFixedChargeSector R r hr) omega



def fkRectVerticalFluxTilt (R : FKRectTorus) (q lam : Real)
    (z : Int) (omega : R.Configuration) : Real :=
  (∑ arrows : SixVertexArrows R.medialTorus,
      if fkOrientedLoopVerticalFlux R.medialTorus arrows = z then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0) /
    fkRectCriticalReducedWeight R q omega



theorem sixVertexUpCount_eq_half_sub_iff_verticalFlux_eq_neg_two_mul
    (T : EvenTorus) (arrows : SixVertexArrows T)
    (r : Nat) (hr : r <= T.width / 2) :
    sixVertexUpCount
          (svTorusVerticalRows T arrows (svFinLast T.height_pos)) =
        T.width / 2 - r ↔
      fkOrientedLoopVerticalFlux T arrows = -(2 * (r : Int)) := by
  constructor
  · exact fkOrientedLoopVerticalFlux_eq_neg_two_mul_of_fixedCharge
      T arrows r hr
  · intro hflux
    rw [fkOrientedLoopVerticalFlux_eq_charge] at hflux
    obtain ⟨k, hk⟩ := T.width_even
    have hhalf : T.width / 2 = k := by omega
    have hrk : r <= k := by rwa [<- hhalf]
    rw [hhalf]
    apply Int.ofNat_inj.mp
    rw [Nat.cast_sub hrk]
    have hkInt : (T.width : Int) = 2 * (k : Int) := by
      have hkTwo : T.width = 2 * k := by omega
      exact_mod_cast hkTwo
    linarith



theorem fkRectFixedChargeTilt_eq_verticalFluxTilt
    (R : FKRectTorus) (q lam : Real)
    (r : Nat) (hr : r <= R.medialTorus.width / 2)
    (omega : R.Configuration) :
    fkRectFixedChargeTilt R q lam r hr omega =
      fkRectVerticalFluxTilt R q lam (-(2 * (r : Int))) omega := by
  unfold fkRectFixedChargeTilt fkRectSignedChargeTilt
    fkRectFixedChargeSector fkRectVerticalFluxTilt
  congr 1
  apply Finset.sum_congr rfl
  intro arrows harrows
  apply if_congr
  · exact sixVertexUpCount_eq_half_sub_iff_verticalFlux_eq_neg_two_mul
      R.medialTorus arrows r hr
  · rfl
  · rfl




theorem sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r <= R.medialTorus.width / 2) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectFixedChargeTilt R q lam r hr omega) =
      sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q := by
  dsimp only [fkRectFixedChargeTilt]
  rw [sum_rcProb_mul_fkRectSignedChargeTilt_eq_canonicalSectorTrace_div_Z
    R hq (fkRectFixedChargeSector R r hr)]
  rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
  rfl




theorem sum_rcProb_mul_fkRectVerticalFluxTilt_eq_partitionSum_div_Z
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r <= R.medialTorus.width / 2) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectVerticalFluxTilt R q lam (-(2 * (r : Int))) omega) =
      sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q := by
  dsimp only
  calc
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectVerticalFluxTilt R q
          (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
          (-(2 * (r : Int))) omega) =
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega *
            fkRectFixedChargeTilt R q
              (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
              r hr omega := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [fkRectFixedChargeTilt_eq_verticalFluxTilt]
    _ = _ :=
      sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
        R hq r hr


theorem sum_rcProb_mul_fkRectFixedChargeTilt_eq_sectorTrace_div_Z
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r <= R.medialTorus.width / 2) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectFixedChargeTilt R q lam r hr omega) =
      Matrix.trace
          (sixVertexSectorTransfer R.medialTorus.width
            (R.medialTorus.width / 2 - r)
            (fkQgt4SixVertexWeight q) ^ R.medialTorus.height) /
        fkRectCriticalReducedZ R q := by
  dsimp only
  rw [sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
    R hq r hr]
  rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]


theorem one_le_fkRectMedial_halfWidth (R : FKRectTorus) :
    1 <= R.medialTorus.width / 2 := by
  change 1 <= (2 * R.width) / 2
  have hwidth := R.width_pos
  omega



theorem sum_rcProb_mul_fkRectOneWindingTilt_eq_partitionSum_div_Z
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    let hOne := one_le_fkRectMedial_halfWidth R
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectFixedChargeTilt R q lam 1 hOne omega) =
      sixVertexTorusFixedChargePartitionSum R.medialTorus 1 hOne
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q := by
  dsimp only
  exact sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
    R hq 1 (one_le_fkRectMedial_halfWidth R)



theorem sum_rcProb_mul_fkRectChargeOneFluxTilt_eq_partitionSum_div_Z
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    let hOne := one_le_fkRectMedial_halfWidth R
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectVerticalFluxTilt R q lam (-2) omega) =
      sixVertexTorusFixedChargePartitionSum R.medialTorus 1 hOne
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q := by
  dsimp only
  simpa using
    (sum_rcProb_mul_fkRectVerticalFluxTilt_eq_partitionSum_div_Z
      R hq 1 (one_le_fkRectMedial_halfWidth R))

end

end StatMech.FrontierD
