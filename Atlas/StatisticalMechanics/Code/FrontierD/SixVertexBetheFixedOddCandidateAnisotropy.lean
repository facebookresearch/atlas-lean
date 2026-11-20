/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy
import Code.FrontierD.SixVertexBetheZeroPhaseSingle

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section

private theorem tendsto_sixVertexFixedOddPairScale :
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

private theorem sixVertexThetaLeftDerivAtZero_add_one_eq
    {c y : Real} (hc : 2 < c) :
    sixVertexThetaLeftDerivAtZero c y + 1 =
      2 * (c ^ 2 + Real.cos y - 1) /
        ((c ^ 2 + Real.cos y - 1) ^ 2 + Real.sin y ^ 2) := by
  have ha : 0 < c ^ 2 + Real.cos y - 1 := by
    nlinarith [Real.neg_one_le_cos y]
  have hden' :
      (c ^ 2 + Real.cos y - 1) ^ 2 + Real.sin y ^ 2 ≠ 0 := by
    positivity
  unfold sixVertexThetaLeftDerivAtZero sixVertexBetheIntegratingFactor
    sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
    sixVertexDelta
  rw [Real.cos_zero, Real.sin_zero, zero_sub]
  rw [show 2 * ((2 - c ^ 2) / 2) = 2 - c ^ 2 by ring, neg_sq]
  have hdeneq :
      (1 + Real.cos y - (2 - c ^ 2)) ^ 2 + Real.sin y ^ 2 =
        (c ^ 2 + Real.cos y - 1) ^ 2 + Real.sin y ^ 2 := by ring
  rw [hdeneq]
  field_simp [hden']
  nlinarith [Real.sin_sq_add_cos_sq y]



theorem tendsto_sixVertexThetaLeftDerivAtZero_atTop
    (y : Real -> Real) :
    Tendsto (fun c => sixVertexThetaLeftDerivAtZero c (y c))
      atTop (nhds (-1)) := by
  have hbound : Tendsto (fun c : Real => 2 / (c ^ 2 - 2))
      atTop (nhds 0) :=
    tendsto_sixVertexFixedOddPairScale.const_div_atTop 2
  have hadd : Tendsto
      (fun c => sixVertexThetaLeftDerivAtZero c (y c) + 1)
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero'
      (Filter.Eventually.of_forall (fun c => norm_nonneg _)) ?_ hbound
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    change ‖sixVertexThetaLeftDerivAtZero c (y c) + 1‖ <=
      2 / (c ^ 2 - 2)
    rw [Real.norm_eq_abs,
      sixVertexThetaLeftDerivAtZero_add_one_eq hc]
    let a := c ^ 2 + Real.cos (y c) - 1
    let d := c ^ 2 - 2
    have hd : 0 < d := by dsimp [d]; nlinarith
    have hda : d <= a := by
      dsimp [d, a]
      linarith [Real.neg_one_le_cos (y c)]
    have ha : 0 < a := hd.trans_le hda
    have hD : 0 < a ^ 2 + Real.sin (y c) ^ 2 := by positivity
    have hnonneg : 0 <= 2 * a /
        (a ^ 2 + Real.sin (y c) ^ 2) := div_nonneg (by positivity) hD.le
    rw [abs_of_nonneg hnonneg]
    rw [div_le_div_iff₀ hD hd]
    have had : a * d <= a ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hda ha.le]
    nlinarith [sq_nonneg (Real.sin (y c))]
  have h := hadd.sub (tendsto_const_nhds :
    Tendsto (fun _ : Real => (1 : Real)) atTop (nhds 1))
  simpa only [add_sub_cancel_right, zero_sub] using h


theorem sixVertexFixedOddCentralLimitingRoot_eq_zero (s k : Nat) :
    sixVertexFixedChargeLimitingRoot (2 * s + 1) k
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) = 0 := by
  unfold sixVertexFixedChargeLimitingRoot
  have hn : sixVertexFixedChargeBetheParticleCount (2 * s + 1) k =
      2 * (s + k + 1) + 1 := by
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    omega
  have hq : sixVertexCentralQuantumNumber
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) = 0 := by
    rw [sixVertexCentralQuantumNumber_eq]
    unfold sixVertexFixedChargeBetheCentralIndex
    change (((sixVertexFixedChargeBetheParticleCount (2 * s + 1) k / 2 : Nat) :
      Real) -
      ((sixVertexFixedChargeBetheParticleCount (2 * s + 1) k : Real) - 1) /
        2) = 0
    rw [hn]
    rw [show (2 * (s + k + 1) + 1) / 2 = s + k + 1 by omega]
    push_cast
    ring
  rw [hq]
  simp

theorem sixVertexFixedOddCentralLimitingPhase_eq_one (s k : Nat) :
    sixVertexFixedChargeLimitingPhase (2 * s + 1) k
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) = 1 := by
  unfold sixVertexFixedChargeLimitingPhase
  rw [sixVertexFixedOddCentralLimitingRoot_eq_zero]
  simp [sixVertexBethePhase]

theorem sixVertexFixedOddLimitingPhase_ne_one_of_ne_central
    (s k : Nat) (j : Fin
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k))
    (hj : j ≠ sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) :
    sixVertexFixedChargeLimitingPhase (2 * s + 1) k j ≠ 1 := by
  intro h
  have heq : sixVertexFixedChargeLimitingPhase (2 * s + 1) k j =
      sixVertexFixedChargeLimitingPhase (2 * s + 1) k
        (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) := by
    rw [sixVertexFixedOddCentralLimitingPhase_eq_one]
    exact h
  exact hj (sixVertexFixedChargeLimitingPhase_injective
    (2 * s + 1) k heq)


def sixVertexFixedOddChargeBethePrefactorNormalized
    (s k : Nat) (c : Real) : Real :=
  if hc : 2 < c then
    sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)
        (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) /
      (c ^ 2 - 2)
  else 0

theorem tendsto_sixVertexFixedOddChargeBethePrefactorNormalized
    (s k : Nat) :
    Tendsto (sixVertexFixedOddChargeBethePrefactorNormalized s k) atTop
      (nhds (sixVertexFixedChargeBetheComplementCount (2 * s + 1) k)) := by
  let r := 2 * s + 1
  let n := sixVertexFixedChargeBetheParticleCount r k
  let N := sixVertexFourWidth r k
  have hderiv : Tendsto
      (fun c => ∑ j : Fin n,
        sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRootAt r k j c))
      atTop (nhds (-(n : Real))) := by
    have hsum := tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_sixVertexThetaLeftDerivAtZero_atTop
        (sixVertexFixedChargeBetheRootAt r k j)
    have hconst : (∑ _j : Fin n, (-1 : Real)) = -(n : Real) := by simp
    rw [hconst] at hsum
    exact hsum
  have hbracket : Tendsto
      (fun c => (N : Real) + ∑ j : Fin n,
        sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRootAt r k j c))
      atTop (nhds (sixVertexFixedChargeBetheComplementCount r k : Real)) := by
    have h := (tendsto_const_nhds : Tendsto
      (fun _ : Real => (N : Real)) atTop (nhds (N : Real))).add hderiv
    convert h using 1
    dsimp [N, n, r]
    rw [sixVertexFixedChargeBetheComplementCount_eq,
      sixVertexFixedChargeBetheParticleCount_eq, sixVertexFourWidth]
    push_cast
    ring
  have hscale : Tendsto (fun c : Real => c ^ 2 / (c ^ 2 - 2))
      atTop (nhds 1) := by
    have hinv : Tendsto (fun c : Real => 2 / (c ^ 2 - 2))
        atTop (nhds 0) :=
      tendsto_sixVertexFixedOddPairScale.const_div_atTop 2
    have h0 := (tendsto_const_nhds : Tendsto
      (fun _ : Real => (1 : Real)) atTop (nhds 1)).add hinv
    have h : Tendsto (fun c : Real => 1 + 2 / (c ^ 2 - 2))
        atTop (nhds 1) := by simpa using h0
    apply h.congr'
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    have hd : c ^ 2 - 2 ≠ 0 := by nlinarith
    field_simp [hd]
    ring
  have hprod : Tendsto
      (fun c => c ^ 2 / (c ^ 2 - 2) *
        ((N : Real) + ∑ j : Fin n,
          sixVertexThetaLeftDerivAtZero c
            (sixVertexFixedChargeBetheRootAt r k j c)))
      atTop (nhds (sixVertexFixedChargeBetheComplementCount
        (2 * s + 1) k : Real)) := by
    simpa [r] using hscale.mul hbracket
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  rw [sixVertexFixedOddChargeBethePrefactorNormalized, dif_pos hc]
  rw [sixVertexZeroPhaseBethePrefactor_eq hc _ _ _
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc
      ⟨s, by omega⟩ k)]
  simp_rw [sixVertexFixedChargeBetheRootAt_eq hc]
  dsimp [r, n, N]
  ring


def sixVertexFixedOddChargeNormalizedMProduct (s k : Nat) (c : Real) : Real :=
  ∏ j ∈ (Finset.univ.erase
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k)),
    ‖sixVertexBetheM c
      (sixVertexBethePhase
        (sixVertexFixedChargeBetheRootAt (2 * s + 1) k j c)) /
      (c ^ 2 - 2 : Real)‖

def sixVertexFixedOddChargeLimitingMProduct (s k : Nat) : Real :=
  ∏ j ∈ (Finset.univ.erase
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k)),
    ‖-1 / (1 - sixVertexFixedChargeLimitingPhase (2 * s + 1) k j)‖

theorem tendsto_sixVertexFixedOddChargeNormalizedMProduct (s k : Nat) :
    Tendsto (sixVertexFixedOddChargeNormalizedMProduct s k) atTop
      (nhds (sixVertexFixedOddChargeLimitingMProduct s k)) := by
  unfold sixVertexFixedOddChargeNormalizedMProduct
    sixVertexFixedOddChargeLimitingMProduct
  apply tendsto_finsetProd
  intro j hj
  have hjne : j ≠ sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k :=
    (Finset.mem_erase.mp hj).1
  exact continuous_norm.continuousAt.tendsto.comp
    (tendsto_sixVertexFixedChargeBetheM_normalized (2 * s + 1) k j
      (sixVertexFixedOddLimitingPhase_ne_one_of_ne_central s k j hjne))



def sixVertexFixedOddChargeBetheCandidateNormalized
    (s k : Nat) (c : Real) : Real :=
  if hc : 2 < c then
    sixVertexFixedOddChargeBetheEigenvalueValue hc (2 * s + 1) k /
      (c ^ 2 - 2) ^
        sixVertexFixedChargeBetheParticleCount (2 * s + 1) k
  else 0

def sixVertexFixedOddChargeBetheCandidateInfinity (s k : Nat) : Real :=
  sixVertexFixedChargeBetheComplementCount (2 * s + 1) k *
    sixVertexFixedOddChargeLimitingMProduct s k

theorem tendsto_sixVertexFixedOddChargeBetheCandidateNormalized
    (s k : Nat) :
    Tendsto (sixVertexFixedOddChargeBetheCandidateNormalized s k) atTop
      (nhds (sixVertexFixedOddChargeBetheCandidateInfinity s k)) := by
  have hprod :=
    (tendsto_sixVertexFixedOddChargeBethePrefactorNormalized s k).mul
      (tendsto_sixVertexFixedOddChargeNormalizedMProduct s k)
  unfold sixVertexFixedOddChargeBetheCandidateInfinity
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  rw [sixVertexFixedOddChargeBetheCandidateNormalized, dif_pos hc]
  unfold sixVertexFixedOddChargeBetheEigenvalueValue
    sixVertexZeroPhaseBetheEigenvalueValue
    sixVertexFixedOddChargeBethePrefactorNormalized
    sixVertexFixedOddChargeNormalizedMProduct
  rw [dif_pos hc]
  simp_rw [sixVertexFixedChargeBetheRootAt_eq hc, norm_div]
  have hdpos : 0 < c ^ 2 - 2 := by nlinarith
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const]
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  have hn : 0 < sixVertexFixedChargeBetheParticleCount (2 * s + 1) k :=
    sixVertexFixedChargeBetheParticleCount_pos _ _
  have hpow : (c ^ 2 - 2) *
      (c ^ 2 - 2) ^
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k - 1) =
      (c ^ 2 - 2) ^
        sixVertexFixedChargeBetheParticleCount (2 * s + 1) k := by
    rw [← pow_succ']
    congr
    omega
  rw [← hpow]
  field_simp [hdpos.ne']

end

end StatMech.FrontierD
