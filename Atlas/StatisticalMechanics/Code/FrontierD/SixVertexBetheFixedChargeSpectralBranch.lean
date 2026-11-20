/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedOddCandidateAnisotropy
import Code.FrontierD.SixVertexBetheFixedChargeVandermonde
import Code.FrontierD.SixVertexPerronSpectralIsolation

open Finset Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexFixedChargeBetheRotatedRealWave
    {c : Real} (hc : 2 < c) (r k : Nat) (a : Complex) :
    SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) -> Real :=
  fun x => (a * sixVertexCoordinateBetheWave c
    (sixVertexFixedChargeBetheRoots hc r k) x).re

theorem sixVertexFixedChargeBetheRotatedRealWave_eigenrelation
    {c μ : Real} (hc : 2 < c) (r k : Nat)
    (hrelation :
      (sixVertexSectorTransferComplex (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c).mulVec
          (sixVertexCoordinateBetheWave c
            (sixVertexFixedChargeBetheRoots hc r k)) =
        (μ : Complex) • sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc r k))
    (a : Complex) :
    sixVertexSectorTransfer (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) c *ᵥ
      sixVertexFixedChargeBetheRotatedRealWave hc r k a =
        μ • sixVertexFixedChargeBetheRotatedRealWave hc r k a := by
  funext x
  have hx := congrFun hrelation x
  change (∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) : Complex) *
        sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc r k) y) =
      (μ : Complex) * sixVertexCoordinateBetheWave c
        (sixVertexFixedChargeBetheRoots hc r k) x at hx
  have hcplx :
      (∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) : Complex) *
          (a * sixVertexCoordinateBetheWave c
            (sixVertexFixedChargeBetheRoots hc r k) y)) =
        (μ : Complex) * (a * sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc r k) x) := by
    calc
      _ = a * (∑ y,
          ((sixVertexSectorTransfer (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) :
              Complex) *
            sixVertexCoordinateBetheWave c
              (sixVertexFixedChargeBetheRoots hc r k) y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
      _ = a * ((μ : Complex) * sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc r k) x) := by rw [hx]
      _ = _ := by ring
  have hre := congrArg Complex.re hcplx
  have hsumre :
      ((∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) :
            Complex) *
          (a * sixVertexCoordinateBetheWave c
            (sixVertexFixedChargeBetheRoots hc r k) y))).re =
        ∑ y, (((sixVertexSectorTransfer (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) :
            Complex) *
          (a * sixVertexCoordinateBetheWave c
            (sixVertexFixedChargeBetheRoots hc r k) y)).re := by
    exact map_sum Complex.reCLM _ _
  rw [hsumre] at hre
  simpa only [sixVertexFixedChargeBetheRotatedRealWave, Matrix.mulVec,
    dotProduct, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hre

theorem exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero_of_coordinate
    {c : Real} (hc : 2 < c) (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : sixVertexCoordinateBetheWave c
      (sixVertexFixedChargeBetheRoots hc r k) x ≠ 0) :
    ∃ a : Complex,
      sixVertexFixedChargeBetheRotatedRealWave hc r k a ≠ 0 := by
  let z := sixVertexCoordinateBetheWave c
    (sixVertexFixedChargeBetheRoots hc r k) x
  refine ⟨star z, ?_⟩
  intro hzero
  have hcoord := congrFun hzero x
  change (star z * z).re = 0 at hcoord
  have hprod : star z * z = (Complex.normSq z : Complex) := by
    calc
      star z * z = z * star z := mul_comm _ _
      _ = (Complex.normSq z : Complex) := by
        simpa only [starRingEnd_apply] using Complex.mul_conj z
  rw [hprod] at hcoord
  norm_num at hcoord
  exact hx hcoord

theorem eventually_exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero
    (r k : Nat) :
    ∀ᶠ c : Real in atTop, ∀ hc : 2 < c,
      ∃ a : Complex,
        sixVertexFixedChargeBetheRotatedRealWave hc r k a ≠ 0 := by
  filter_upwards
    [eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero r k,
      eventually_gt_atTop (2 : Real)] with c hwave hc
  intro hc'
  obtain ⟨x, hx⟩ := Function.ne_iff.mp (hwave hc')
  exact exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero_of_coordinate
    hc' r k x (by simpa using hx)

private theorem sixVertexFixedChargeNormalized_hasEigenvalue_of_realWave
    {c μ : Real} (hc : 2 < c) (r k : Nat) (a : Complex)
    (hne : sixVertexFixedChargeBetheRotatedRealWave hc r k a ≠ 0)
    (heig : sixVertexSectorTransfer (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) c *ᵥ
      sixVertexFixedChargeBetheRotatedRealWave hc r k a =
        μ • sixVertexFixedChargeBetheRotatedRealWave hc r k a) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized
        (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) c))
      (μ / (c ^ 2 - 2) ^
        sixVertexFixedChargeBetheParticleCount r k) := by
  let z : EuclideanSpace Real (SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :=
    WithLp.toLp 2 (sixVertexFixedChargeBetheRotatedRealWave hc r k a)
  have hz : z ≠ 0 := by
    intro h
    apply hne
    apply WithLp.toLp_injective
    exact h
  have hraw : Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransfer (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) c)) μ := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := z)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hz⟩
    apply WithLp.ofLp_injective 2
    simpa [z, Matrix.ofLp_toLpLin] using heig
  exact sixVertexSectorTransferNormalized_hasEigenvalue
    (pow_ne_zero _ (by nlinarith)) hraw

theorem eventually_sixVertexFixedEvenChargeBetheCandidateNormalized_hasEigenvalue
    (s k : Nat) :
    ∀ᶠ c : Real in atTop,
      Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized
          (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k) c))
        (sixVertexFixedEvenChargeBetheCandidateNormalized s k c) := by
  filter_upwards
    [eventually_exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero
      (2 * s) k, eventually_gt_atTop (2 : Real)] with c hnon hc
  obtain ⟨a, ha⟩ := hnon hc
  rw [sixVertexFixedEvenChargeBetheCandidateNormalized, dif_pos hc]
  apply sixVertexFixedChargeNormalized_hasEigenvalue_of_realWave hc (2 * s) k a ha
  apply sixVertexFixedChargeBetheRotatedRealWave_eigenrelation hc
  exact sixVertexFixedEvenChargeBetheRoots_eigenrelation_value hc s k

theorem eventually_sixVertexFixedOddChargeBetheCandidateNormalized_hasEigenvalue
    (s k : Nat) :
    ∀ᶠ c : Real in atTop,
      Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized
          (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) c))
        (sixVertexFixedOddChargeBetheCandidateNormalized s k c) := by
  filter_upwards
    [eventually_exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero
      (2 * s + 1) k, eventually_gt_atTop (2 : Real)] with c hnon hc
  obtain ⟨a, ha⟩ := hnon hc
  rw [sixVertexFixedOddChargeBetheCandidateNormalized, dif_pos hc]
  apply sixVertexFixedChargeNormalized_hasEigenvalue_of_realWave hc
    (2 * s + 1) k a ha
  apply sixVertexFixedChargeBetheRotatedRealWave_eigenrelation hc
  exact sixVertexFixedChargeBetheRoots_zeroPhaseEigenrelation_value_of_odd_charge
    hc ⟨s, by omega⟩ k

end

end StatMech.FrontierD
