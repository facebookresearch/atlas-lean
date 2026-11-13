/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargeInfinityWave
import Code.FrontierD.SixVertexPerronInfinity

open Finset Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeCoordinateBetheWave_eq_scale_mul_normalizedWave
    {c : Real} (hc : 2 < c) (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k) x =
      sixVertexFixedChargePairScaleProduct r k c *
        sixVertexFixedChargeNormalizedWave r k c x := by
  unfold sixVertexCoordinateBetheWave sixVertexFixedChargeNormalizedWave
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  simp_rw [sixVertexFixedChargeBetheRootAt_eq hc]
  have hamp : sixVertexBetheAmplitude c
      (sixVertexFixedChargeBetheRoots hc r k) sigma =
      sixVertexFixedChargePairScaleProduct r k c *
        sixVertexFixedChargeNormalizedAmplitude r k c sigma := by
    unfold sixVertexBetheAmplitude sixVertexFixedChargeNormalizedAmplitude
      sixVertexBethePairProduct sixVertexFixedChargePairScaleProduct
    simp_rw [sixVertexFixedChargeBetheRootAt_eq hc]
    have hprod :
        (∏ i, ∏ j ∈ Finset.Ioi i,
          sixVertexBethePairFactor c
            (sixVertexBethePhase
              (sixVertexFixedChargeBetheRoots hc r k (sigma i)))
            (sixVertexBethePhase
              (sixVertexFixedChargeBetheRoots hc r k (sigma j)))) =
        (∏ i : Fin (sixVertexFixedChargeBetheParticleCount r k),
          ∏ _j ∈ Finset.Ioi i,
          ((c ^ 2 - 2 : Real) : Complex)) *
        (∏ i, ∏ j ∈ Finset.Ioi i,
          sixVertexNormalizedBethePairFactor c
            (sixVertexBethePhase
              (sixVertexFixedChargeBetheRoots hc r k (sigma i)))
            (sixVertexBethePhase
              (sixVertexFixedChargeBetheRoots hc r k (sigma j)))) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      unfold sixVertexNormalizedBethePairFactor
      have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by
        norm_cast
        nlinarith
      field_simp [hd]
    rw [hprod]
    ring
  rw [hamp]
  ring

theorem sixVertexFixedChargeNormalizedWave_eigenrelation
    {c μ : Real} (hc : 2 < c) (r k : Nat)
    (hrelation :
      (sixVertexSectorTransferComplex (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c).mulVec
          (sixVertexCoordinateBetheWave c
            (sixVertexFixedChargeBetheRoots hc r k)) =
        (μ : Complex) • sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc r k)) :
    ∀ x, ∑ y,
        ((sixVertexSectorTransferNormalized (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) : Complex) *
            sixVertexFixedChargeNormalizedWave r k c y =
      ((μ / (c ^ 2 - 2) ^
          sixVertexFixedChargeBetheParticleCount r k : Real) : Complex) *
        sixVertexFixedChargeNormalizedWave r k c x := by
  intro x
  have hx := congrFun hrelation x
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx
  simp_rw [sixVertexFixedChargeCoordinateBetheWave_eq_scale_mul_normalizedWave
    hc r k] at hx
  have hscale := sixVertexFixedChargePairScaleProduct_ne_zero hc r k
  have hraw :
      (∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) : Complex) *
          sixVertexFixedChargeNormalizedWave r k c y) =
        (μ : Complex) * sixVertexFixedChargeNormalizedWave r k c x := by
    apply mul_left_cancel₀ hscale
    calc
      sixVertexFixedChargePairScaleProduct r k c *
          ∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) :
              Complex) * sixVertexFixedChargeNormalizedWave r k c y =
        ∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) :
              Complex) *
            (sixVertexFixedChargePairScaleProduct r k c *
              sixVertexFixedChargeNormalizedWave r k c y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
      _ = (μ : Complex) *
          (sixVertexFixedChargePairScaleProduct r k c *
            sixVertexFixedChargeNormalizedWave r k c x) := hx
      _ = sixVertexFixedChargePairScaleProduct r k c *
          ((μ : Complex) *
            sixVertexFixedChargeNormalizedWave r k c x) := by ring
  have hdenR : (c ^ 2 - 2) ^
      sixVertexFixedChargeBetheParticleCount r k ≠ 0 := by
    apply pow_ne_zero
    nlinarith
  unfold sixVertexSectorTransferNormalized
  push_cast
  have hdenC : (((c : Complex) ^ 2 - 2) ^
      sixVertexFixedChargeBetheParticleCount r k) ≠ 0 := by
    apply pow_ne_zero
    norm_cast
    nlinarith
  calc
    (∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) : Complex) /
        (((c : Complex) ^ 2 - 2) ^
          sixVertexFixedChargeBetheParticleCount r k) *
            sixVertexFixedChargeNormalizedWave r k c y) =
      (∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) :
            Complex) * sixVertexFixedChargeNormalizedWave r k c y) /
        (((c : Complex) ^ 2 - 2) ^
          sixVertexFixedChargeBetheParticleCount r k) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y _
        ring
    _ = (((μ : Complex) /
          (((c : Complex) ^ 2 - 2) ^
            sixVertexFixedChargeBetheParticleCount r k)) *
        sixVertexFixedChargeNormalizedWave r k c x) := by
      rw [hraw]
      field_simp [hdenC]

private theorem tendsto_fixedChargeNormalizedWave_mulVec
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto (fun c => ∑ y,
        ((sixVertexSectorTransferNormalized (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) : Complex) *
            sixVertexFixedChargeNormalizedWave r k c y)
      atTop (nhds (∑ y,
        ((sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x y : Real) : Complex) *
            sixVertexFixedChargeLimitingWave r k y)) := by
  apply tendsto_finsetSum Finset.univ
  intro y _
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_sixVertexSectorTransfer_normalized_atTop
        (sixVertexFixedChargeBetheParticleCount_pos r k) x y)).mul
    (tendsto_sixVertexFixedChargeNormalizedWave r k y)

theorem sixVertexFixedEvenChargeLimitingWave_eigenrelation
    (s k : Nat) :
    ∀ x, ∑ y,
        sixVertexSectorTransferInfinity (sixVertexFourWidth (2 * s) k)
            (sixVertexFixedChargeBetheParticleCount (2 * s) k) x y *
          sixVertexFixedChargeLimitingWave (2 * s) k y =
      (sixVertexFixedEvenChargeBetheCandidateInfinity s k : Complex) *
        sixVertexFixedChargeLimitingWave (2 * s) k x := by
  intro x
  have hevent : ∀ᶠ c : Real in atTop,
      (∑ y,
        ((sixVertexSectorTransferNormalized (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k) c x y : Real) :
            Complex) * sixVertexFixedChargeNormalizedWave (2 * s) k c y) =
      (sixVertexFixedEvenChargeBetheCandidateNormalized s k c : Complex) *
        sixVertexFixedChargeNormalizedWave (2 * s) k c x := by
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    rw [sixVertexFixedEvenChargeBetheCandidateNormalized, dif_pos hc]
    exact sixVertexFixedChargeNormalizedWave_eigenrelation hc (2 * s) k
      (sixVertexFixedEvenChargeBetheRoots_eigenrelation_value hc s k) x
  have hleft := tendsto_fixedChargeNormalizedWave_mulVec (2 * s) k x
  have hright :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_sixVertexFixedEvenChargeBetheCandidateNormalized s k)).mul
        (tendsto_sixVertexFixedChargeNormalizedWave (2 * s) k x)
  have hevent' : (fun c =>
      (sixVertexFixedEvenChargeBetheCandidateNormalized s k c : Complex) *
        sixVertexFixedChargeNormalizedWave (2 * s) k c x) =ᶠ[atTop]
      (fun c => ∑ y,
        ((sixVertexSectorTransferNormalized (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k) c x y : Real) :
            Complex) * sixVertexFixedChargeNormalizedWave (2 * s) k c y) := by
    filter_upwards [hevent] with c hc
    exact hc.symm
  have heq := tendsto_nhds_unique hleft (hright.congr' hevent')
  simpa using heq

theorem sixVertexFixedOddChargeLimitingWave_eigenrelation
    (s k : Nat) :
    ∀ x, ∑ y,
        sixVertexSectorTransferInfinity (sixVertexFourWidth (2 * s + 1) k)
            (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) x y *
          sixVertexFixedChargeLimitingWave (2 * s + 1) k y =
      (sixVertexFixedOddChargeBetheCandidateInfinity s k : Complex) *
        sixVertexFixedChargeLimitingWave (2 * s + 1) k x := by
  intro x
  have hevent : ∀ᶠ c : Real in atTop,
      (∑ y,
        ((sixVertexSectorTransferNormalized (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) c x y :
            Real) : Complex) *
              sixVertexFixedChargeNormalizedWave (2 * s + 1) k c y) =
      (sixVertexFixedOddChargeBetheCandidateNormalized s k c : Complex) *
        sixVertexFixedChargeNormalizedWave (2 * s + 1) k c x := by
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    rw [sixVertexFixedOddChargeBetheCandidateNormalized, dif_pos hc]
    exact sixVertexFixedChargeNormalizedWave_eigenrelation hc (2 * s + 1) k
      (sixVertexFixedChargeBetheRoots_zeroPhaseEigenrelation_value_of_odd_charge
        hc ⟨s, by omega⟩ k) x
  have hleft := tendsto_fixedChargeNormalizedWave_mulVec (2 * s + 1) k x
  have hright :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_sixVertexFixedOddChargeBetheCandidateNormalized s k)).mul
        (tendsto_sixVertexFixedChargeNormalizedWave (2 * s + 1) k x)
  have hevent' : (fun c =>
      (sixVertexFixedOddChargeBetheCandidateNormalized s k c : Complex) *
        sixVertexFixedChargeNormalizedWave (2 * s + 1) k c x) =ᶠ[atTop]
      (fun c => ∑ y,
        ((sixVertexSectorTransferNormalized
          (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) c x y :
            Real) : Complex) *
              sixVertexFixedChargeNormalizedWave (2 * s + 1) k c y) := by
    filter_upwards [hevent] with c hc
    exact hc.symm
  have heq := tendsto_nhds_unique hleft (hright.congr' hevent')
  simpa using heq

end

end StatMech.FrontierD
