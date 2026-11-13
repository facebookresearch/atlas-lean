/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargeInfinityEigenrelation
import Code.FrontierD.SixVertexBetheFixedChargeInfinityPositive

open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



def sixVertexFixedChargePositiveInfinityWave (r k : Nat) :
    SixVertexNoAdjacentSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) -> Real :=
  fun x => ((-Complex.I) ^ sixVertexFixedChargeBethePairCount r k *
    sixVertexFixedChargeLimitingWave r k x.1).re

theorem sixVertexFixedChargePositiveInfinityWave_pos
    (r k : Nat)
    (x : SixVertexNoAdjacentSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    0 < sixVertexFixedChargePositiveInfinityWave r k x := by
  exact sixVertexFixedChargeLimitingWave_rotated_re_pos_of_noAdjacent
    r k x.1 x.2

private theorem noAdjacent_eigenvalue_eq_infinityTop
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n <= N)
    (mu : Real) (v : SixVertexNoAdjacentSector N n -> Real)
    (hv : forall i, 0 < v i)
    (heig : sixVertexNoAdjacentTransferInfinity N n *ᵥ v = mu • v) :
    mu = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
  classical
  letI : Nonempty (SixVertexNoAdjacentSector N n) :=
    ⟨sixVertexNoAdjacentAlternatingEven N n hn hhalf⟩
  obtain ⟨u, hupos, hueig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let S : Real := ∑ i, u i * v i
  have hS : 0 < S := by
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hupos i) (hv i)
    · exact Finset.univ_nonempty
  have hadj :
      ∑ i, u i * (sixVertexNoAdjacentTransferInfinity N n *ᵥ v) i =
        ∑ i, (sixVertexNoAdjacentTransferInfinity N n *ᵥ
          (fun j => u j)) i * v i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [sixVertexNoAdjacentTransferInfinity_symmetric N n]
    ring
  have hmu : (∑ i, u i * (sixVertexNoAdjacentTransferInfinity N n *ᵥ v) i) =
      mu * S := by
    rw [heig]
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold S
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htop : (∑ i, (sixVertexNoAdjacentTransferInfinity N n *ᵥ
      (fun j => u j)) i * v i) =
      sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf * S := by
    rw [hueig]
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold S
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmu, htop] at hadj
  nlinarith

private theorem active_rotated_eigenrelation_of_full
    (r k : Nat) (mu : Real)
    (hfull : forall x, ∑ y,
      sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x y *
        sixVertexFixedChargeLimitingWave r k y =
      (mu : Complex) * sixVertexFixedChargeLimitingWave r k x) :
    sixVertexNoAdjacentTransferInfinity (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) *ᵥ
      sixVertexFixedChargePositiveInfinityWave r k =
        mu • sixVertexFixedChargePositiveInfinityWave r k := by
  classical
  funext x
  let a : Complex :=
    (-Complex.I) ^ sixVertexFixedChargeBethePairCount r k
  have hx := hfull x.1
  have hrot := congrArg Complex.re (congrArg (fun z : Complex => a * z) hx)
  have hrestrict :
      (∑ y : SixVertexSector (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k),
        sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) x.1 y *
          (a * sixVertexFixedChargeLimitingWave r k y).re) =
      ∑ y : SixVertexNoAdjacentSector (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k),
        sixVertexNoAdjacentTransferInfinity (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) x y *
          (a * sixVertexFixedChargeLimitingWave r k y.1).re := by
    calc
      _ = ∑ y ∈ (Finset.univ.filter fun y : SixVertexSector
            (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) =>
            SixVertexSectorNoAdjacent y),
          sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
              (sixVertexFixedChargeBetheParticleCount r k) x.1 y *
            (a * sixVertexFixedChargeLimitingWave r k y).re := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : SixVertexSectorNoAdjacent y
        · simp [hy]
        · rw [sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_right
            x.1 hy]
          simp [hy]
      _ = _ := Finset.sum_subtype _ (by intro y; simp) _
  have hrealSum :
      (a * ∑ y,
        (sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x.1 y : Complex) *
            sixVertexFixedChargeLimitingWave r k y).re =
      ∑ y, sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x.1 y *
        (a * sixVertexFixedChargeLimitingWave r k y).re := by
    rw [Finset.mul_sum]
    change Complex.reCLM (∑ y,
        a * ((sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x.1 y : Complex) *
            sixVertexFixedChargeLimitingWave r k y)) = _
    rw [map_sum Complex.reCLM]
    apply Finset.sum_congr rfl
    intro y _
    change (a *
        ((sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x.1 y : Complex) *
            sixVertexFixedChargeLimitingWave r k y)).re =
      sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x.1 y *
        (a * sixVertexFixedChargeLimitingWave r k y).re
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, zero_add]
    ring
  change (∑ y, sixVertexNoAdjacentTransferInfinity
      (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) x y *
        sixVertexFixedChargePositiveInfinityWave r k y) =
    mu * sixVertexFixedChargePositiveInfinityWave r k x
  unfold sixVertexFixedChargePositiveInfinityWave
  change (∑ y, sixVertexNoAdjacentTransferInfinity
      (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) x y *
        (a * sixVertexFixedChargeLimitingWave r k y.1).re) =
    mu * (a * sixVertexFixedChargeLimitingWave r k x.1).re
  rw [← hrestrict, ← hrealSum]
  calc
    (a * ∑ y,
      (sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) x.1 y : Complex) *
          sixVertexFixedChargeLimitingWave r k y).re =
        (a * ((mu : Complex) *
          sixVertexFixedChargeLimitingWave r k x.1)).re := hrot
    _ = mu * (a * sixVertexFixedChargeLimitingWave r k x.1).re := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, zero_add]
      ring

theorem sixVertexFixedEvenChargeBetheCandidateInfinity_eq_Perron
    (s k : Nat) :
    sixVertexFixedEvenChargeBetheCandidateInfinity s k =
      sixVertexNoAdjacentInfinityTopEigenvalue
        (sixVertexFourWidth (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount_pos (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k) := by
  apply noAdjacent_eigenvalue_eq_infinityTop
    (sixVertexFixedChargeBetheParticleCount_pos (2 * s) k)
    (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k)
    (sixVertexFixedEvenChargeBetheCandidateInfinity s k)
    (sixVertexFixedChargePositiveInfinityWave (2 * s) k)
    (sixVertexFixedChargePositiveInfinityWave_pos (2 * s) k)
  exact active_rotated_eigenrelation_of_full (2 * s) k
    (sixVertexFixedEvenChargeBetheCandidateInfinity s k)
    (sixVertexFixedEvenChargeLimitingWave_eigenrelation s k)

theorem sixVertexFixedOddChargeBetheCandidateInfinity_eq_Perron
    (s k : Nat) :
    sixVertexFixedOddChargeBetheCandidateInfinity s k =
      sixVertexNoAdjacentInfinityTopEigenvalue
        (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount_pos (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k) := by
  apply noAdjacent_eigenvalue_eq_infinityTop
    (sixVertexFixedChargeBetheParticleCount_pos (2 * s + 1) k)
    (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k)
    (sixVertexFixedOddChargeBetheCandidateInfinity s k)
    (sixVertexFixedChargePositiveInfinityWave (2 * s + 1) k)
    (sixVertexFixedChargePositiveInfinityWave_pos (2 * s + 1) k)
  exact active_rotated_eigenrelation_of_full (2 * s + 1) k
    (sixVertexFixedOddChargeBetheCandidateInfinity s k)
    (sixVertexFixedOddChargeLimitingWave_eigenrelation s k)

end

end StatMech.FrontierD
