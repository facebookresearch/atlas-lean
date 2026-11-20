/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheAnisotropyRoots
import Code.FrontierD.SixVertexBetheSpectralIsolation
import Mathlib.LinearAlgebra.Vandermonde

open Finset Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section

private theorem tendsto_sixVertexPairScale :
    Tendsto (fun c : Real => c ^ 2 - 2) atTop atTop := by
  have hsq : Tendsto (fun c : Real => c * c) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with c hc
    have hc1 : 1 <= c := le_trans (le_max_left _ _) hc
    have hcb : b <= c := le_trans (le_max_right _ _) hc
    nlinarith
  simpa only [pow_two, sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-2) hsq)


def sixVertexNormalizedBethePairFactor (c : Real) (u v : Complex) : Complex :=
  sixVertexBethePairFactor c u v / (c ^ 2 - 2 : Real)

theorem tendsto_sixVertexNormalizedBethePairFactorAt (k : Nat)
    (i j : Fin ((k + 1) + (k + 1))) :
    Tendsto
      (fun c => sixVertexNormalizedBethePairFactor c
        (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c))
        (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c)))
      atTop (nhds (sixVertexHalfFilledLimitingPhase k i)) := by
  let u : Real -> Complex := fun c =>
    sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c)
  let v : Real -> Complex := fun c =>
    sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c)
  let u0 := sixVertexHalfFilledLimitingPhase k i
  let v0 := sixVertexHalfFilledLimitingPhase k j
  have hu : Tendsto u atTop (nhds u0) :=
    tendsto_sixVertexHalfFilledBethePhaseAt k i
  have hv : Tendsto v atTop (nhds v0) :=
    tendsto_sixVertexHalfFilledBethePhaseAt k j
  have hinvR : Tendsto (fun c : Real => 1 / (c ^ 2 - 2))
      atTop (nhds 0) := tendsto_sixVertexPairScale.const_div_atTop 1
  have hinvC : Tendsto
      (fun c : Real => Complex.ofReal (1 / (c ^ 2 - 2)))
      atTop (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR
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
        (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c))
        (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c)) =
      1 + sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c) *
          sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c) +
        ((c ^ 2 - 2 : Real) : Complex) *
          sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c) := by
        unfold sixVertexBethePairFactor sixVertexDelta
        push_cast
        ring
    _ = (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c) +
          (1 + sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c) *
            sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c)) *
              Complex.ofReal (1 / (c ^ 2 - 2))) *
        ((c ^ 2 - 2 : Real) : Complex) := by
      rw [add_mul, mul_assoc, hinv, mul_one]
      ring


def sixVertexHalfFilledNormalizedAmplitude (k : Nat) (c : Real)
    (sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))) : Complex :=
  (((Equiv.Perm.sign sigma : Int) : Complex)) *
    ∏ i, ∏ j ∈ Finset.Ioi i,
      sixVertexNormalizedBethePairFactor c
        (sixVertexBethePhase
          (sixVertexHalfFilledBetheRootAt k (sigma i) c))
        (sixVertexBethePhase
          (sixVertexHalfFilledBetheRootAt k (sigma j) c))

theorem tendsto_sixVertexHalfFilledNormalizedAmplitude (k : Nat)
    (sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))) :
    Tendsto (sixVertexHalfFilledNormalizedAmplitude k · sigma) atTop
      (nhds ((((Equiv.Perm.sign sigma : Int) : Complex)) *
        ∏ i, ∏ _j ∈ Finset.Ioi i,
          sixVertexHalfFilledLimitingPhase k (sigma i))) := by
  unfold sixVertexHalfFilledNormalizedAmplitude
  apply tendsto_const_nhds.mul
  apply tendsto_finsetProd Finset.univ
  intro i _
  apply tendsto_finsetProd (Finset.Ioi i)
  intro j _
  exact tendsto_sixVertexNormalizedBethePairFactorAt k (sigma i) (sigma j)

private theorem tendsto_sixVertexHalfFilledOddMonomial (k : Nat)
    (sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))) :
    Tendsto
      (fun c => sixVertexBetheMonomial
        (fun j => sixVertexHalfFilledBetheRootAt k j c) sigma
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega)))
      atTop
      (nhds (∏ i, sixVertexHalfFilledLimitingPhase k (sigma i) ^
        (2 * i.val + 1))) := by
  unfold sixVertexBetheMonomial
  simp only [sixVertexSectorPosition_alternatingOdd_apply_val]
  apply tendsto_finsetProd Finset.univ
  intro i _
  exact (tendsto_sixVertexHalfFilledBethePhaseAt k (sigma i)).pow
    (2 * i.val + 1)



def sixVertexHalfFilledNormalizedOddWave (k : Nat) (c : Real) : Complex :=
  ∑ sigma : Equiv.Perm (Fin ((k + 1) + (k + 1))),
    sixVertexHalfFilledNormalizedAmplitude k c sigma *
      sixVertexBetheMonomial
        (fun j => sixVertexHalfFilledBetheRootAt k j c) sigma
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega))


def sixVertexHalfFilledVandermondeSum (k : Nat) : Complex :=
  ∑ sigma : Equiv.Perm (Fin ((k + 1) + (k + 1))),
    (((Equiv.Perm.sign sigma : Int) : Complex)) *
      (∏ i, ∏ _j ∈ Finset.Ioi i,
        sixVertexHalfFilledLimitingPhase k (sigma i)) *
      ∏ i, sixVertexHalfFilledLimitingPhase k (sigma i) ^
        (2 * i.val + 1)

theorem tendsto_sixVertexHalfFilledNormalizedOddWave (k : Nat) :
    Tendsto (sixVertexHalfFilledNormalizedOddWave k) atTop
      (nhds (sixVertexHalfFilledVandermondeSum k)) := by
  unfold sixVertexHalfFilledNormalizedOddWave
    sixVertexHalfFilledVandermondeSum
  apply tendsto_finsetSum Finset.univ
  intro sigma _
  exact (tendsto_sixVertexHalfFilledNormalizedAmplitude k sigma).mul
    (tendsto_sixVertexHalfFilledOddMonomial k sigma)

private theorem bethe_vandermonde_permutation_sum {n : Nat}
    (z : Fin n -> Complex) :
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
        ((∏ i, z (sigma i) ^ n) * ∏ i, z (sigma i) ^ i.val) := by
      rw [hcombine]
    _ = (∏ i, z (sigma i) ^ n) *
        (↑↑(Equiv.Perm.sign sigma) * ∏ i, z (sigma i) ^ i.val) := by
      ring

theorem sixVertexHalfFilledVandermondeSum_eq (k : Nat) :
    sixVertexHalfFilledVandermondeSum k =
      (∏ i, sixVertexHalfFilledLimitingPhase k i ^
        ((k + 1) + (k + 1))) *
      (Matrix.vandermonde (sixVertexHalfFilledLimitingPhase k)).det := by
  exact bethe_vandermonde_permutation_sum
    (sixVertexHalfFilledLimitingPhase k)

theorem sixVertexHalfFilledVandermondeSum_ne_zero (k : Nat) :
    sixVertexHalfFilledVandermondeSum k ≠ 0 := by
  rw [sixVertexHalfFilledVandermondeSum_eq]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero _ (Complex.exp_ne_zero _)
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (sixVertexHalfFilledLimitingPhase_injective k)


def sixVertexHalfFilledPairScaleProduct (k : Nat) (c : Real) : Complex :=
  ∏ i : Fin ((k + 1) + (k + 1)),
    ∏ _j ∈ Finset.Ioi i, ((c ^ 2 - 2 : Real) : Complex)

theorem sixVertexHalfFilledPairScaleProduct_ne_zero
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexHalfFilledPairScaleProduct k c ≠ 0 := by
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by
    norm_cast
    nlinarith
  unfold sixVertexHalfFilledPairScaleProduct
  exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
    Finset.prod_ne_zero_iff.mpr (fun j _ => hd))

private theorem sixVertexBethePairProduct_eq_scale_mul_normalized
    {c : Real} (hc : 2 < c) (k : Nat)
    (sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))) :
    sixVertexBethePairProduct c (sixVertexHalfFilledBetheRoots hc k) sigma =
      sixVertexHalfFilledPairScaleProduct k c *
        ∏ i, ∏ j ∈ Finset.Ioi i,
          sixVertexNormalizedBethePairFactor c
            (sixVertexBethePhase
              (sixVertexHalfFilledBetheRoots hc k (sigma i)))
            (sixVertexBethePhase
              (sixVertexHalfFilledBetheRoots hc k (sigma j))) := by
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by
    norm_cast
    nlinarith
  unfold sixVertexBethePairProduct sixVertexHalfFilledPairScaleProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  unfold sixVertexNormalizedBethePairFactor
  field_simp [hd]

private theorem sixVertexBetheAmplitude_eq_scale_mul_normalized
    {c : Real} (hc : 2 < c) (k : Nat)
    (sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))) :
    sixVertexBetheAmplitude c (sixVertexHalfFilledBetheRoots hc k) sigma =
      sixVertexHalfFilledPairScaleProduct k c *
        sixVertexHalfFilledNormalizedAmplitude k c sigma := by
  unfold sixVertexBetheAmplitude sixVertexHalfFilledNormalizedAmplitude
  simp_rw [sixVertexHalfFilledBetheRootAt_eq hc]
  rw [sixVertexBethePairProduct_eq_scale_mul_normalized hc k sigma]
  ring



theorem sixVertexCoordinateBetheWave_odd_eq_scale_mul_normalized
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexCoordinateBetheWave c (sixVertexHalfFilledBetheRoots hc k)
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega)) =
      sixVertexHalfFilledPairScaleProduct k c *
        sixVertexHalfFilledNormalizedOddWave k c := by
  unfold sixVertexCoordinateBetheWave sixVertexHalfFilledNormalizedOddWave
  simp_rw [sixVertexHalfFilledBetheRootAt_eq hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [sixVertexBetheAmplitude_eq_scale_mul_normalized hc k sigma]
  ring



theorem exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero_of_coordinate
    {c : Real} (hc : 2 < c) (k : Nat)
    (x : SixVertexSector (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)))
    (hx : sixVertexCoordinateBetheWave c
      (sixVertexHalfFilledBetheRoots hc k) x ≠ 0) :
    ∃ a : Complex, sixVertexHalfFilledBetheRotatedRealWave hc k a ≠ 0 := by
  let z := sixVertexCoordinateBetheWave c
    (sixVertexHalfFilledBetheRoots hc k) x
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
  have hz : z ≠ 0 := hx
  norm_num at hcoord
  exact hz hcoord




theorem eventually_exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero
    (k : Nat) :
    ∀ᶠ c : Real in atTop, ∀ hc : 2 < c,
      ∃ a : Complex, sixVertexHalfFilledBetheRotatedRealWave hc k a ≠ 0 := by
  have hnormalized : ∀ᶠ c : Real in atTop,
      sixVertexHalfFilledNormalizedOddWave k c ≠ 0 :=
    (tendsto_sixVertexHalfFilledNormalizedOddWave k).eventually_ne
      (sixVertexHalfFilledVandermondeSum_ne_zero k)
  filter_upwards [hnormalized, eventually_gt_atTop (2 : Real)] with c hnonzero hc
  intro hc'
  have heval : sixVertexCoordinateBetheWave c
      (sixVertexHalfFilledBetheRoots hc' k)
      (sixVertexAlternatingOddSector
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega)) ≠ 0 := by
    rw [sixVertexCoordinateBetheWave_odd_eq_scale_mul_normalized hc' k]
    exact mul_ne_zero
      (sixVertexHalfFilledPairScaleProduct_ne_zero hc' k) hnonzero
  exact exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero_of_coordinate
    hc' k _ heval



theorem eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top_vandermonde
    (k : Nat) :
    ∀ᶠ c : Real in atTop,
      sixVertexHalfFilledBetheCandidateNormalized k c =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega) c /
          (c ^ 2 - 2) ^ ((k + 1) + (k + 1)) :=
  eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top k
    (eventually_exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero k)



theorem eventually_sixVertexHalfFilledBetheCandidate_eq_top_vandermonde
    (k : Nat) :
    ∀ᶠ c : Real in atTop, ∀ hc : 2 < c,
      sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexPositiveHalfBetheRoots hc k) =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega) c := by
  filter_upwards
    [eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top_vandermonde k,
      eventually_gt_atTop (2 : Real)] with c heq hc
  intro hc'
  rw [sixVertexHalfFilledBetheCandidateNormalized, dif_pos hc'] at heq
  have hscale : (c ^ 2 - 2) ^ ((k + 1) + (k + 1)) ≠ 0 := by
    exact pow_ne_zero _ (by nlinarith)
  field_simp [hscale] at heq
  exact heq

end

end StatMech.FrontierD
