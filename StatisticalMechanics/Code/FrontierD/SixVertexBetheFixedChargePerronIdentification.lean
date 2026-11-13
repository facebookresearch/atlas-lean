/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargeInfinityPositive
import Code.FrontierD.SixVertexBetheFixedChargeInfinityEigenrelation

open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



def sixVertexFixedChargeLimitingRotatedActiveWave (r k : Nat) :
    SixVertexNoAdjacentSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) → Real :=
  fun x ↦ ((-Complex.I) ^ sixVertexFixedChargeBethePairCount r k *
    sixVertexFixedChargeLimitingWave r k x.1).re

theorem sixVertexFixedChargeLimitingRotatedActiveWave_pos
    (r k : Nat)
    (x : SixVertexNoAdjacentSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    0 < sixVertexFixedChargeLimitingRotatedActiveWave r k x := by
  exact sixVertexFixedChargeLimitingWave_rotated_re_pos_of_noAdjacent
    r k x.1 x.2

private theorem sixVertexFixedChargeLimitingRotatedActiveWave_eigenrelation
    (r k : Nat) (mu : Real)
    (hfull : ∀ x, ∑ y,
        sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) x y *
          sixVertexFixedChargeLimitingWave r k y =
      (mu : Complex) * sixVertexFixedChargeLimitingWave r k x) :
    sixVertexNoAdjacentTransferInfinity (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) *ᵥ
      sixVertexFixedChargeLimitingRotatedActiveWave r k =
        mu • sixVertexFixedChargeLimitingRotatedActiveWave r k := by
  classical
  funext x
  let a : Complex := (-Complex.I) ^ sixVertexFixedChargeBethePairCount r k
  have hx := hfull x.1
  have hsum :
      (∑ y : SixVertexSector (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k),
        (sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x.1 y : Complex) *
            sixVertexFixedChargeLimitingWave r k y) =
      ∑ y : SixVertexNoAdjacentSector (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k),
        (sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x.1 y.1 : Complex) *
            sixVertexFixedChargeLimitingWave r k y.1 := by
    calc
      _ = ∑ y ∈ (Finset.univ.filter fun y : SixVertexSector
            (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) ↦
              SixVertexSectorNoAdjacent y),
          (sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) x.1 y : Complex) *
              sixVertexFixedChargeLimitingWave r k y := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : SixVertexSectorNoAdjacent y
        · simp [hy]
        · rw [sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_right
            x.1 hy]
          simp [hy]
      _ = _ := Finset.sum_subtype _ (by simp) _
  change (∑ y, (sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) x.1 y : Complex) *
        sixVertexFixedChargeLimitingWave r k y) = _ at hx
  rw [hsum] at hx
  have hamul := congrArg (fun z : Complex ↦ a * z) hx
  dsimp only at hamul
  rw [Finset.mul_sum] at hamul
  have hre := congrArg Complex.re hamul
  have hsumre :
      ((∑ y : SixVertexNoAdjacentSector (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k),
        a * ((sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x.1 y.1 : Complex) *
            sixVertexFixedChargeLimitingWave r k y.1))).re =
      ∑ y : SixVertexNoAdjacentSector (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k),
        (a * ((sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x.1 y.1 : Complex) *
            sixVertexFixedChargeLimitingWave r k y.1)).re := by
    exact map_sum Complex.reCLM _ _
  rw [hsumre] at hre
  have hterm (y : SixVertexNoAdjacentSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
      (a * ((sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) x.1 y.1 : Complex) *
          sixVertexFixedChargeLimitingWave r k y.1)).re =
      sixVertexNoAdjacentTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x y *
        (a * sixVertexFixedChargeLimitingWave r k y.1).re := by
    unfold sixVertexNoAdjacentTransferInfinity
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, sub_zero]
    ring
  simp_rw [hterm] at hre
  have hright :
      (a * ((mu : Complex) *
        sixVertexFixedChargeLimitingWave r k x.1)).re =
      mu * (a * sixVertexFixedChargeLimitingWave r k x.1).re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, sub_zero]
    ring
  rw [hright] at hre
  simpa only [Matrix.mulVec, dotProduct,
    sixVertexFixedChargeLimitingRotatedActiveWave,
    Pi.smul_apply, smul_eq_mul, a] using hre



theorem sixVertexNoAdjacentInfinity_eigenvalue_eq_top_of_positive_eigenvector
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N)
    {mu : Real} (q : SixVertexNoAdjacentSector N n → Real)
    (hqpos : ∀ i, 0 < q i)
    (hq : sixVertexNoAdjacentTransferInfinity N n *ᵥ q = mu • q) :
    mu = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
  classical
  letI : Nonempty (SixVertexNoAdjacentSector N n) :=
    ⟨sixVertexNoAdjacentAlternatingEven N n hn hhalf⟩
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let S : Real := ∑ i, v i * q i
  have hS : 0 < S := by
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hvpos i) (hqpos i)
    · exact Finset.univ_nonempty
  have hadj : ∑ i, v i *
      (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) i =
      ∑ i, (sixVertexNoAdjacentTransferInfinity N n *ᵥ
        (fun j ↦ v j)) i * q i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [sixVertexNoAdjacentTransferInfinity_symmetric N n]
    ring
  have hleft : ∑ i, v i *
      (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) i = mu * S := by
    rw [hq]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : ∑ i,
      (sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun j ↦ v j)) i * q i =
      sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf * S := by
    rw [hveig]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft, hright] at hadj
  nlinarith

theorem sixVertexFixedEvenChargeBetheCandidateInfinity_eq_Perron
    (s k : Nat) :
    sixVertexFixedEvenChargeBetheCandidateInfinity s k =
      sixVertexNoAdjacentInfinityTopEigenvalue
        (sixVertexFourWidth (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount_pos (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k) := by
  apply sixVertexNoAdjacentInfinity_eigenvalue_eq_top_of_positive_eigenvector
    (sixVertexFixedChargeBetheParticleCount_pos (2 * s) k)
    (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k)
    (sixVertexFixedChargeLimitingRotatedActiveWave (2 * s) k)
    (sixVertexFixedChargeLimitingRotatedActiveWave_pos (2 * s) k)
  exact sixVertexFixedChargeLimitingRotatedActiveWave_eigenrelation
    (2 * s) k (sixVertexFixedEvenChargeBetheCandidateInfinity s k)
    (sixVertexFixedEvenChargeLimitingWave_eigenrelation s k)

theorem sixVertexFixedOddChargeBetheCandidateInfinity_eq_Perron
    (s k : Nat) :
    sixVertexFixedOddChargeBetheCandidateInfinity s k =
      sixVertexNoAdjacentInfinityTopEigenvalue
        (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount_pos (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k) := by
  apply sixVertexNoAdjacentInfinity_eigenvalue_eq_top_of_positive_eigenvector
    (sixVertexFixedChargeBetheParticleCount_pos (2 * s + 1) k)
    (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k)
    (sixVertexFixedChargeLimitingRotatedActiveWave (2 * s + 1) k)
    (sixVertexFixedChargeLimitingRotatedActiveWave_pos (2 * s + 1) k)
  exact sixVertexFixedChargeLimitingRotatedActiveWave_eigenrelation
    (2 * s + 1) k (sixVertexFixedOddChargeBetheCandidateInfinity s k)
    (sixVertexFixedOddChargeLimitingWave_eigenrelation s k)

end

end StatMech.FrontierD
