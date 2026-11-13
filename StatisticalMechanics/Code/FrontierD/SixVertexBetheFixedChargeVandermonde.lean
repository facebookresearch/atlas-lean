/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots
import Code.FrontierD.SixVertexBetheVandermonde










open Finset Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section

private theorem tendsto_sixVertexFixedChargePairScale :
    Tendsto (fun c : Real => c ^ 2 - 2) atTop atTop := by
  have hsq : Tendsto (fun c : Real => c * c) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with c hc
    have hc1 : 1 ≤ c := le_trans (le_max_left _ _) hc
    have hcb : b ≤ c := le_trans (le_max_right _ _) hc
    nlinarith
  simpa only [pow_two, sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-2) hsq)

theorem tendsto_sixVertexFixedChargeNormalizedBethePairFactorAt
    (r k : Nat)
    (i j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto
      (fun c => sixVertexNormalizedBethePairFactor c
        (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c))
        (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)))
      atTop (nhds (sixVertexFixedChargeLimitingPhase r k i)) := by
  let u : Real → Complex := fun c =>
    sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c)
  let v : Real → Complex := fun c =>
    sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)
  let u0 := sixVertexFixedChargeLimitingPhase r k i
  let v0 := sixVertexFixedChargeLimitingPhase r k j
  have hu : Tendsto u atTop (nhds u0) :=
    tendsto_sixVertexFixedChargeBethePhaseAt r k i
  have hv : Tendsto v atTop (nhds v0) :=
    tendsto_sixVertexFixedChargeBethePhaseAt r k j
  have hinvR : Tendsto (fun c : Real => 1 / (c ^ 2 - 2))
      atTop (nhds 0) := tendsto_sixVertexFixedChargePairScale.const_div_atTop 1
  have hinvC : Tendsto
      (fun c : Real => Complex.ofReal (1 / (c ^ 2 - 2)))
      atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR
  have hlimit : Tendsto
      (fun c => u c + (1 + u c * v c) *
        Complex.ofReal (1 / (c ^ 2 - 2)))
      atTop (nhds u0) := by
    simpa using hu.add ((tendsto_const_nhds.add (hu.mul hv)).mul hinvC)
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  have hd : c ^ 2 - 2 ≠ 0 := by nlinarith
  have hdC : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by exact_mod_cast hd
  have hinv : Complex.ofReal (1 / (c ^ 2 - 2)) *
      ((c ^ 2 - 2 : Real) : Complex) = 1 := by
    rw [← Complex.ofReal_mul]
    field_simp [hd]
    norm_num
  dsimp [u, v]
  unfold sixVertexNormalizedBethePairFactor
  rw [eq_div_iff hdC]
  symm
  calc
    sixVertexBethePairFactor c
        (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c))
        (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)) =
      1 + sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c) *
          sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c) +
        ((c ^ 2 - 2 : Real) : Complex) *
          sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c) := by
        unfold sixVertexBethePairFactor sixVertexDelta
        push_cast
        ring
    _ = (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c) +
          (1 + sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k i c) *
            sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)) *
              Complex.ofReal (1 / (c ^ 2 - 2))) *
        ((c ^ 2 - 2 : Real) : Complex) := by
      rw [add_mul, mul_assoc, hinv, mul_one]
      ring

def sixVertexFixedChargeNormalizedAmplitude (r k : Nat) (c : Real)
    (sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    Complex :=
  (((Equiv.Perm.sign sigma : Int) : Complex)) *
    ∏ i, ∏ j ∈ Finset.Ioi i,
      sixVertexNormalizedBethePairFactor c
        (sixVertexBethePhase
          (sixVertexFixedChargeBetheRootAt r k (sigma i) c))
        (sixVertexBethePhase
          (sixVertexFixedChargeBetheRootAt r k (sigma j) c))

theorem tendsto_sixVertexFixedChargeNormalizedAmplitude (r k : Nat)
    (sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    Tendsto (sixVertexFixedChargeNormalizedAmplitude r k · sigma) atTop
      (nhds ((((Equiv.Perm.sign sigma : Int) : Complex)) *
        ∏ i, ∏ _j ∈ Finset.Ioi i,
          sixVertexFixedChargeLimitingPhase r k (sigma i))) := by
  unfold sixVertexFixedChargeNormalizedAmplitude
  apply tendsto_const_nhds.mul
  apply tendsto_finsetProd Finset.univ
  intro i _
  apply tendsto_finsetProd (Finset.Ioi i)
  intro j _
  exact tendsto_sixVertexFixedChargeNormalizedBethePairFactorAt
    r k (sigma i) (sigma j)

private theorem tendsto_sixVertexFixedChargeAlternatingMonomial
    (r k : Nat)
    (sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    Tendsto
      (fun c => sixVertexBetheMonomial
        (fun j => sixVertexFixedChargeBetheRootAt r k j c) sigma
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k)
          (sixVertexFixedChargeBetheParticleCount_twice_le r k)))
      atTop
      (nhds (∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^
        (2 * i.val + 1))) := by
  unfold sixVertexBetheMonomial
  simp only [sixVertexSectorPosition_alternatingOdd_apply_val]
  apply tendsto_finsetProd Finset.univ
  intro i _
  exact (tendsto_sixVertexFixedChargeBethePhaseAt r k (sigma i)).pow
    (2 * i.val + 1)

def sixVertexFixedChargeNormalizedAlternatingWave
    (r k : Nat) (c : Real) : Complex :=
  ∑ sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k)),
    sixVertexFixedChargeNormalizedAmplitude r k c sigma *
      sixVertexBetheMonomial
        (fun j => sixVertexFixedChargeBetheRootAt r k j c) sigma
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k)
          (sixVertexFixedChargeBetheParticleCount_twice_le r k))

def sixVertexFixedChargeVandermondeSum (r k : Nat) : Complex :=
  ∑ sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k)),
    (((Equiv.Perm.sign sigma : Int) : Complex)) *
      (∏ i, ∏ _j ∈ Finset.Ioi i,
        sixVertexFixedChargeLimitingPhase r k (sigma i)) *
      ∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^
        (2 * i.val + 1)

theorem tendsto_sixVertexFixedChargeNormalizedAlternatingWave (r k : Nat) :
    Tendsto (sixVertexFixedChargeNormalizedAlternatingWave r k) atTop
      (nhds (sixVertexFixedChargeVandermondeSum r k)) := by
  unfold sixVertexFixedChargeNormalizedAlternatingWave
    sixVertexFixedChargeVandermondeSum
  apply tendsto_finsetSum Finset.univ
  intro sigma _
  exact (tendsto_sixVertexFixedChargeNormalizedAmplitude r k sigma).mul
    (tendsto_sixVertexFixedChargeAlternatingMonomial r k sigma)

private theorem fixedCharge_bethe_vandermonde_permutation_sum {n : Nat}
    (z : Fin n → Complex) :
    (∑ sigma : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign sigma : Int) : Complex)) *
        (∏ i, ∏ _j ∈ Finset.Ioi i, z (sigma i)) *
        ∏ i, z (sigma i) ^ (2 * i.val + 1)) =
      (∏ i, z i ^ n) * (Matrix.vandermonde z).det := by
  have hpairs (sigma : Equiv.Perm (Fin n)) :
      (∏ i, ∏ _j ∈ Finset.Ioi i, z (sigma i)) =
        ∏ i, z (sigma i) ^ (n - 1 - i.val) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_const, Fin.card_Ioi]
  rw [Matrix.det_apply', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [hpairs]
  have hreindex : (∏ i, z i ^ n) = ∏ i, z (sigma i) ^ n := by
    simpa using (Equiv.prod_comp sigma (fun i => z i ^ n)).symm
  rw [hreindex]
  simp only [Matrix.vandermonde_apply]
  have hcombine :
      (∏ i, z (sigma i) ^ (n - 1 - i.val)) *
          (∏ i, z (sigma i) ^ (2 * i.val + 1)) =
        (∏ i, z (sigma i) ^ n) *
          ∏ i, z (sigma i) ^ i.val := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_add, ← pow_add]
    have hi := i.isLt
    rw [show n - 1 - i.val + (2 * i.val + 1) = n + i.val by omega]
  calc
    (↑↑(Equiv.Perm.sign sigma) *
          ∏ i, z (sigma i) ^ (n - 1 - i.val)) *
        ∏ i, z (sigma i) ^ (2 * i.val + 1) =
      ↑↑(Equiv.Perm.sign sigma) *
        ((∏ i, z (sigma i) ^ (n - 1 - i.val)) *
          ∏ i, z (sigma i) ^ (2 * i.val + 1)) := by ring
    _ = ↑↑(Equiv.Perm.sign sigma) *
        ((∏ i, z (sigma i) ^ n) *
          ∏ i, z (sigma i) ^ i.val) := by rw [hcombine]
    _ = (∏ i, z (sigma i) ^ n) *
        (↑↑(Equiv.Perm.sign sigma) *
          ∏ i, z (sigma i) ^ i.val) := by ring

theorem sixVertexFixedChargeVandermondeSum_eq (r k : Nat) :
    sixVertexFixedChargeVandermondeSum r k =
      (∏ i, sixVertexFixedChargeLimitingPhase r k i ^
        sixVertexFixedChargeBetheParticleCount r k) *
      (Matrix.vandermonde
        (sixVertexFixedChargeLimitingPhase r k)).det :=
  fixedCharge_bethe_vandermonde_permutation_sum
    (sixVertexFixedChargeLimitingPhase r k)

theorem sixVertexFixedChargeVandermondeSum_ne_zero (r k : Nat) :
    sixVertexFixedChargeVandermondeSum r k ≠ 0 := by
  rw [sixVertexFixedChargeVandermondeSum_eq]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero _ (Complex.exp_ne_zero _)
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (sixVertexFixedChargeLimitingPhase_injective r k)

def sixVertexFixedChargePairScaleProduct (r k : Nat) (c : Real) : Complex :=
  ∏ i : Fin (sixVertexFixedChargeBetheParticleCount r k),
    ∏ _j ∈ Finset.Ioi i, ((c ^ 2 - 2 : Real) : Complex)

theorem sixVertexFixedChargePairScaleProduct_ne_zero
    {c : Real} (hc : 2 < c) (r k : Nat) :
    sixVertexFixedChargePairScaleProduct r k c ≠ 0 := by
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by
    norm_cast
    nlinarith
  unfold sixVertexFixedChargePairScaleProduct
  exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
    Finset.prod_ne_zero_iff.mpr (fun j _ => hd))

private theorem sixVertexFixedChargeBethePairProduct_eq_scale_mul_normalized
    {c : Real} (hc : 2 < c) (r k : Nat)
    (sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    sixVertexBethePairProduct c (sixVertexFixedChargeBetheRoots hc r k) sigma =
      sixVertexFixedChargePairScaleProduct r k c *
        ∏ i, ∏ j ∈ Finset.Ioi i,
          sixVertexNormalizedBethePairFactor c
            (sixVertexBethePhase
              (sixVertexFixedChargeBetheRoots hc r k (sigma i)))
            (sixVertexBethePhase
              (sixVertexFixedChargeBetheRoots hc r k (sigma j))) := by
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by
    norm_cast
    nlinarith
  unfold sixVertexBethePairProduct sixVertexFixedChargePairScaleProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  unfold sixVertexNormalizedBethePairFactor
  field_simp [hd]

private theorem sixVertexFixedChargeBetheAmplitude_eq_scale_mul_normalized
    {c : Real} (hc : 2 < c) (r k : Nat)
    (sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    sixVertexBetheAmplitude c (sixVertexFixedChargeBetheRoots hc r k) sigma =
      sixVertexFixedChargePairScaleProduct r k c *
        sixVertexFixedChargeNormalizedAmplitude r k c sigma := by
  unfold sixVertexBetheAmplitude sixVertexFixedChargeNormalizedAmplitude
  simp_rw [sixVertexFixedChargeBetheRootAt_eq hc]
  rw [sixVertexFixedChargeBethePairProduct_eq_scale_mul_normalized hc r k sigma]
  ring

theorem sixVertexFixedChargeCoordinateBetheWave_alternating_eq
    {c : Real} (hc : 2 < c) (r k : Nat) :
    sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k)
          (sixVertexFixedChargeBetheParticleCount_twice_le r k)) =
      sixVertexFixedChargePairScaleProduct r k c *
        sixVertexFixedChargeNormalizedAlternatingWave r k c := by
  unfold sixVertexCoordinateBetheWave
    sixVertexFixedChargeNormalizedAlternatingWave
  simp_rw [sixVertexFixedChargeBetheRootAt_eq hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [sixVertexFixedChargeBetheAmplitude_eq_scale_mul_normalized hc r k sigma]
  ring

theorem eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero
    (r k : Nat) :
    ∀ᶠ c : Real in atTop, ∀ hc : 2 < c,
      sixVertexCoordinateBetheWave (N := sixVertexFourWidth r k) c
        (sixVertexFixedChargeBetheRoots hc r k) ≠ 0 := by
  have hnormalized : ∀ᶠ c : Real in atTop,
      sixVertexFixedChargeNormalizedAlternatingWave r k c ≠ 0 :=
    (tendsto_sixVertexFixedChargeNormalizedAlternatingWave r k).eventually_ne
      (sixVertexFixedChargeVandermondeSum_ne_zero r k)
  filter_upwards [hnormalized, eventually_gt_atTop (2 : Real)] with
      c hnonzero hc
  intro hc' hwave
  have heval := congrFun hwave
    (sixVertexAlternatingOddSector
      (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)
      (sixVertexFixedChargeBetheParticleCount_twice_le r k))
  rw [sixVertexFixedChargeCoordinateBetheWave_alternating_eq hc' r k] at heval
  exact (mul_ne_zero
    (sixVertexFixedChargePairScaleProduct_ne_zero hc' r k) hnonzero) heval

end

end StatMech.FrontierD
