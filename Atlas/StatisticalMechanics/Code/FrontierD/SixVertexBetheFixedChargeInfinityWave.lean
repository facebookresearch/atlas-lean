/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargeSpectralBranch
import Mathlib.LinearAlgebra.Vandermonde

open Finset Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexFixedChargeLimitingMonomial (r k : Nat)
    (sigma : Equiv.Perm
      (Fin (sixVertexFixedChargeBetheParticleCount r k)))
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) : Complex :=
  ∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^
    (sixVertexSectorPosition x i).val


def sixVertexFixedChargeNormalizedWave (r k : Nat) (c : Real)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) : Complex :=
  ∑ sigma : Equiv.Perm
      (Fin (sixVertexFixedChargeBetheParticleCount r k)),
    sixVertexFixedChargeNormalizedAmplitude r k c sigma *
      sixVertexBetheMonomial
        (fun j => sixVertexFixedChargeBetheRootAt r k j c) sigma x


def sixVertexFixedChargeLimitingWave (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) : Complex :=
  ∑ sigma : Equiv.Perm
      (Fin (sixVertexFixedChargeBetheParticleCount r k)),
    (((Equiv.Perm.sign sigma : Int) : Complex)) *
      (∏ i, ∏ _j ∈ Finset.Ioi i,
        sixVertexFixedChargeLimitingPhase r k (sigma i)) *
      sixVertexFixedChargeLimitingMonomial r k sigma x

theorem tendsto_sixVertexFixedChargeLimitingMonomial
    (r k : Nat)
    (sigma : Equiv.Perm
      (Fin (sixVertexFixedChargeBetheParticleCount r k)))
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto
      (fun c => sixVertexBetheMonomial
        (fun j => sixVertexFixedChargeBetheRootAt r k j c) sigma x)
      atTop (nhds (sixVertexFixedChargeLimitingMonomial r k sigma x)) := by
  unfold sixVertexBetheMonomial sixVertexFixedChargeLimitingMonomial
  apply tendsto_finsetProd Finset.univ
  intro i _
  exact (tendsto_sixVertexFixedChargeBethePhaseAt r k (sigma i)).pow
    (sixVertexSectorPosition x i).val

theorem tendsto_sixVertexFixedChargeNormalizedWave
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto (fun c => sixVertexFixedChargeNormalizedWave r k c x) atTop
      (nhds (sixVertexFixedChargeLimitingWave r k x)) := by
  unfold sixVertexFixedChargeNormalizedWave sixVertexFixedChargeLimitingWave
  apply tendsto_finsetSum Finset.univ
  intro sigma _
  exact (tendsto_sixVertexFixedChargeNormalizedAmplitude r k sigma).mul
    (tendsto_sixVertexFixedChargeLimitingMonomial r k sigma x)



def sixVertexFixedChargeAlternantExponent (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (i : Fin (sixVertexFixedChargeBetheParticleCount r k)) : Nat :=
  (sixVertexSectorPosition x i).val +
    (sixVertexFixedChargeBetheParticleCount r k - 1 - i.val)

private theorem sixVertexFixedChargeLimitingPairProduct_eq
    (r k : Nat)
    (sigma : Equiv.Perm
      (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    (∏ i, ∏ _j ∈ Finset.Ioi i,
        sixVertexFixedChargeLimitingPhase r k (sigma i)) =
      ∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^
        (sixVertexFixedChargeBetheParticleCount r k - 1 - i.val) := by
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_const, Fin.card_Ioi]

theorem sixVertexFixedChargeLimitingWave_eq_alternant
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingWave r k x =
      ∑ sigma : Equiv.Perm
          (Fin (sixVertexFixedChargeBetheParticleCount r k)),
        (((Equiv.Perm.sign sigma : Int) : Complex)) *
          ∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^
            sixVertexFixedChargeAlternantExponent r k x i := by
  unfold sixVertexFixedChargeLimitingWave
    sixVertexFixedChargeLimitingMonomial
  apply Finset.sum_congr rfl
  intro sigma _
  rw [sixVertexFixedChargeLimitingPairProduct_eq]
  rw [mul_assoc]
  rw [← Finset.prod_mul_distrib]
  apply congrArg (fun z : Complex =>
    (((Equiv.Perm.sign sigma : Int) : Complex)) * z)
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add]
  congr 1
  unfold sixVertexFixedChargeAlternantExponent
  omega



def sixVertexFixedChargeAlternantMatrix (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    Matrix (Fin (sixVertexFixedChargeBetheParticleCount r k))
      (Fin (sixVertexFixedChargeBetheParticleCount r k)) Complex :=
  fun j i => sixVertexFixedChargeLimitingPhase r k j ^
    sixVertexFixedChargeAlternantExponent r k x i

theorem sixVertexFixedChargeLimitingWave_eq_det_alternant
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingWave r k x =
      (sixVertexFixedChargeAlternantMatrix r k x).det := by
  rw [sixVertexFixedChargeLimitingWave_eq_alternant]
  rw [Matrix.det_apply']
  rfl


def sixVertexFixedChargeLimitingPhaseStep (r k : Nat) : Complex :=
  Complex.exp (Complex.I *
    (2 * Real.pi / (sixVertexFixedChargeBetheComplementCount r k : Real)))


def sixVertexFixedChargeLimitingPhaseCenter (r k : Nat) : Complex :=
  Complex.exp (-Complex.I *
    (Real.pi *
      (sixVertexFixedChargeBetheParticleCount r k - 1 : Nat) /
        (sixVertexFixedChargeBetheComplementCount r k : Real)))

theorem sixVertexFixedChargeLimitingPhase_eq_geometric
    (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingPhase r k j =
      sixVertexFixedChargeLimitingPhaseCenter r k *
        sixVertexFixedChargeLimitingPhaseStep r k ^ j.val := by
  unfold sixVertexFixedChargeLimitingPhase sixVertexFixedChargeLimitingRoot
    sixVertexFixedChargeLimitingPhaseCenter
    sixVertexFixedChargeLimitingPhaseStep sixVertexBethePhase
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  rw [sixVertexCentralQuantumNumber_eq]
  push_cast [Nat.cast_sub (by
    exact sixVertexFixedChargeBetheParticleCount_pos r k)]
  have hm : (sixVertexFixedChargeBetheComplementCount r k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFixedChargeBetheComplementCount_pos r k).ne'
  field_simp [hm]
  ring



def sixVertexFixedChargeAlternantPoint (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (i : Fin (sixVertexFixedChargeBetheParticleCount r k)) : Complex :=
  sixVertexFixedChargeLimitingPhaseStep r k ^
    sixVertexFixedChargeAlternantExponent r k x i

private theorem alternant_sum_eq_center_mul_vandermonde
    {n : Nat} (a b : Complex) (e : Fin n -> Nat) :
    (∑ sigma : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign sigma : Int) : Complex)) *
        ∏ i, (a * b ^ (sigma i).val) ^ e i) =
      (∏ i, a ^ e i) * (Matrix.vandermonde (fun i => b ^ e i)).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  simp only [Matrix.transpose_apply, Matrix.vandermonde_apply]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  have hpows : (∏ i, (b ^ (sigma i).val) ^ e i) =
      ∏ i, (b ^ e i) ^ (sigma i).val := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, ← pow_mul]
    congr 1
    exact Nat.mul_comm _ _
  rw [hpows]
  ring

theorem sixVertexFixedChargeLimitingWave_eq_center_mul_vandermonde
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingWave r k x =
      (∏ i, sixVertexFixedChargeLimitingPhaseCenter r k ^
        sixVertexFixedChargeAlternantExponent r k x i) *
      (Matrix.vandermonde
        (sixVertexFixedChargeAlternantPoint r k x)).det := by
  rw [sixVertexFixedChargeLimitingWave_eq_alternant]
  simp_rw [sixVertexFixedChargeLimitingPhase_eq_geometric]
  exact alternant_sum_eq_center_mul_vandermonde
    (sixVertexFixedChargeLimitingPhaseCenter r k)
    (sixVertexFixedChargeLimitingPhaseStep r k)
    (sixVertexFixedChargeAlternantExponent r k x)

end

end StatMech.FrontierD
