/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheEvenCandidate
import Code.FrontierD.SixVertexBetheFixedChargeVandermonde

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexFixedEvenPositiveBetheIndex (s k : Nat) (j : Fin (s + k + 1)) :
    Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) :=
  Fin.cast (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm
    (Fin.natAdd (s + k + 1) j)


def sixVertexFixedEvenPositiveBetheRootAt (s k : Nat)
    (j : Fin (s + k + 1)) (c : Real) : Real :=
  sixVertexFixedChargeBetheRootAt (2 * s) k
    (sixVertexFixedEvenPositiveBetheIndex s k j) c


def sixVertexFixedEvenPositiveLimitingRoot (s k : Nat)
    (j : Fin (s + k + 1)) : Real :=
  sixVertexFixedChargeLimitingRoot (2 * s) k
    (sixVertexFixedEvenPositiveBetheIndex s k j)

theorem sixVertexFixedEvenPositiveBetheRootAt_eq
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexFixedEvenPositiveBetheRootAt s k j c =
      sixVertexFixedEvenPositiveBetheRoots hc s k j := by
  unfold sixVertexFixedEvenPositiveBetheRootAt
    sixVertexFixedEvenPositiveBetheIndex
    sixVertexFixedEvenPositiveBetheRoots
    sixVertexFixedEvenChargeBetheRoots
  rw [sixVertexFixedChargeBetheRootAt_eq hc]

theorem tendsto_sixVertexFixedEvenPositiveBetheRootAt
    (s k : Nat) (j : Fin (s + k + 1)) :
    Tendsto (sixVertexFixedEvenPositiveBetheRootAt s k j) atTop
      (nhds (sixVertexFixedEvenPositiveLimitingRoot s k j)) := by
  exact tendsto_sixVertexFixedChargeBetheRootAt (2 * s) k
    (sixVertexFixedEvenPositiveBetheIndex s k j)

theorem sixVertexFixedEvenPositiveLimitingRoot_pos
    (s k : Nat) (j : Fin (s + k + 1)) :
    0 < sixVertexFixedEvenPositiveLimitingRoot s k j := by
  have hm : (0 : Real) <
      (sixVertexFixedChargeBetheComplementCount (2 * s) k : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheComplementCount_pos (2 * s) k
  unfold sixVertexFixedEvenPositiveLimitingRoot
    sixVertexFixedChargeLimitingRoot
  apply div_pos
  · apply mul_pos (mul_pos (by norm_num) Real.pi_pos)
    rw [sixVertexCentralQuantumNumber_eq]
    unfold sixVertexFixedEvenPositiveBetheIndex
    simp only [Fin.val_cast, Fin.natAdd]
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    have hj0 : (0 : Real) <= j.val := by positivity
    push_cast
    nlinarith
  · exact hm

theorem sixVertexFixedEvenPositiveLimitingPhase_ne_one
    (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexBethePhase (sixVertexFixedEvenPositiveLimitingRoot s k j) ≠ 1 := by
  intro h
  have hphase0 :
      sixVertexBethePhase (sixVertexFixedEvenPositiveLimitingRoot s k j) =
        sixVertexBethePhase 0 := by
    simpa [sixVertexBethePhase] using h
  have hroot := sixVertexBethePhase_injective_on_Ioo
    (sixVertexFixedChargeLimitingRoot_mem_Ioo (2 * s) k
      (sixVertexFixedEvenPositiveBetheIndex s k j))
    ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩ hphase0
  exact (sixVertexFixedEvenPositiveLimitingRoot_pos s k j).ne' hroot

private theorem tendsto_sixVertexFixedEvenPairScale :
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

private theorem tendsto_sixVertexFixedChargeSquare_div_pairScale :
    Tendsto (fun c : Real => c ^ 2 / (c ^ 2 - 2)) atTop (nhds 1) := by
  have hinv : Tendsto (fun c : Real => 2 / (c ^ 2 - 2))
      atTop (nhds 0) :=
    tendsto_sixVertexFixedEvenPairScale.const_div_atTop 2
  have heq : (fun c : Real => c ^ 2 / (c ^ 2 - 2)) =ᶠ[atTop]
      fun c => 1 + 2 / (c ^ 2 - 2) := by
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    have hd : c ^ 2 - 2 ≠ 0 := by nlinarith
    field_simp [hd]
    ring
  have hadd : Tendsto (fun c : Real => 1 + 2 / (c ^ 2 - 2))
      atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : Real => (1 : Real))
        atTop (nhds 1)).add hinv)
  exact hadd.congr' heq.symm

private theorem tendsto_sixVertexFixedChargePairScale_inv_complex :
    Tendsto (fun c : Real => ((1 / (c ^ 2 - 2) : Real) : Complex))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun c : Real => 1 / (c ^ 2 - 2))
      atTop (nhds 0) :=
    tendsto_sixVertexFixedEvenPairScale.const_div_atTop 1
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal



theorem tendsto_sixVertexFixedChargeBetheM_normalized
    (r k : Nat) (j : Fin (sixVertexFixedChargeBetheParticleCount r k))
    (hphase : sixVertexFixedChargeLimitingPhase r k j ≠ 1) :
    Tendsto
      (fun c => sixVertexBetheM c
          (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)) /
        (c ^ 2 - 2 : Real))
      atTop
      (nhds (-1 / (1 - sixVertexFixedChargeLimitingPhase r k j))) := by
  let z : Real -> Complex := fun c =>
    sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)
  let z0 : Complex := sixVertexFixedChargeLimitingPhase r k j
  have hz : Tendsto z atTop (nhds z0) :=
    tendsto_sixVertexFixedChargeBethePhaseAt r k j
  have hden : 1 - z0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hphase)
  have hratioReal := tendsto_sixVertexFixedChargeSquare_div_pairScale
  have hratio : Tendsto
      (fun c : Real => (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)))
      atTop (nhds 1) := by
    change Tendsto
      (fun c : Real => Complex.ofReal (c ^ 2 / (c ^ 2 - 2)))
      atTop (nhds (Complex.ofReal 1))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hratioReal
  have hmain : Tendsto
      (fun c => (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)) / (1 - z c))
      atTop (nhds (1 / (1 - z0))) :=
    hratio.div (tendsto_const_nhds.sub hz) hden
  have hlimit0 :=
    tendsto_sixVertexFixedChargePairScale_inv_complex.sub hmain
  have hlimit : Tendsto
      (fun c => ((1 / (c ^ 2 - 2) : Real) : Complex) -
        (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)) / (1 - z c))
      atTop (nhds (-1 / (1 - z0))) := by
    convert hlimit0 using 1 <;> simp [div_eq_mul_inv]
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  have hdR : c ^ 2 - 2 ≠ 0 := by nlinarith
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by exact_mod_cast hdR
  dsimp [z]
  unfold sixVertexBetheM
  push_cast
  field_simp [hd]

theorem tendsto_sixVertexFixedEvenPositiveBetheM_normalized
    (s k : Nat) (j : Fin (s + k + 1)) :
    Tendsto
      (fun c => sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexFixedEvenPositiveBetheRootAt s k j c)) /
        (c ^ 2 - 2 : Real))
      atTop
      (nhds (-1 / (1 - sixVertexBethePhase
        (sixVertexFixedEvenPositiveLimitingRoot s k j)))) := by
  let z : Real -> Complex := fun c => sixVertexBethePhase
    (sixVertexFixedEvenPositiveBetheRootAt s k j c)
  let z0 : Complex := sixVertexBethePhase
    (sixVertexFixedEvenPositiveLimitingRoot s k j)
  have hz : Tendsto z atTop (nhds z0) := by
    have hcontinuous : Continuous (fun p : Real => sixVertexBethePhase p) := by
      unfold sixVertexBethePhase
      fun_prop
    exact hcontinuous.continuousAt.tendsto.comp
      (tendsto_sixVertexFixedEvenPositiveBetheRootAt s k j)
  have hden : 1 - z0 ≠ 0 := sub_ne_zero.mpr
    (Ne.symm (sixVertexFixedEvenPositiveLimitingPhase_ne_one s k j))
  have hratioReal := tendsto_sixVertexFixedChargeSquare_div_pairScale
  have hratio : Tendsto
      (fun c : Real => (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)))
      atTop (nhds 1) := by
    change Tendsto
      (fun c : Real => Complex.ofReal (c ^ 2 / (c ^ 2 - 2)))
      atTop (nhds (Complex.ofReal 1))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hratioReal
  have hmain : Tendsto
      (fun c => (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)) / (1 - z c))
      atTop (nhds (1 / (1 - z0))) :=
    hratio.div (tendsto_const_nhds.sub hz) hden
  have hlimit0 :=
    tendsto_sixVertexFixedChargePairScale_inv_complex.sub hmain
  have hlimit : Tendsto
      (fun c => ((1 / (c ^ 2 - 2) : Real) : Complex) -
        (((c ^ 2 / (c ^ 2 - 2) : Real) : Complex)) / (1 - z c))
      atTop (nhds (-1 / (1 - z0))) := by
    convert hlimit0 using 1 <;> simp [div_eq_mul_inv]
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  have hdR : c ^ 2 - 2 ≠ 0 := by nlinarith
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by exact_mod_cast hdR
  dsimp [z]
  unfold sixVertexBetheM
  push_cast
  field_simp [hd]


def sixVertexFixedEvenPositiveLimitingMNormSq (s k : Nat)
    (j : Fin (s + k + 1)) : Real :=
  1 / (2 - 2 * Real.cos (sixVertexFixedEvenPositiveLimitingRoot s k j))

theorem tendsto_sixVertexFixedEvenPositiveBetheM_normSq_normalized
    (s k : Nat) (j : Fin (s + k + 1)) :
    Tendsto
      (fun c => Complex.normSq
          (sixVertexBetheM c
            (sixVertexBethePhase
              (sixVertexFixedEvenPositiveBetheRootAt s k j c)) /
            (c ^ 2 - 2 : Real)))
      atTop (nhds (sixVertexFixedEvenPositiveLimitingMNormSq s k j)) := by
  have h := (Complex.continuous_normSq.continuousAt.tendsto.comp
    (tendsto_sixVertexFixedEvenPositiveBetheM_normalized s k j))
  convert h using 1
  rw [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_one]
  have hden : Complex.normSq (1 - sixVertexBethePhase
      (sixVertexFixedEvenPositiveLimitingRoot s k j)) =
      2 - 2 * Real.cos (sixVertexFixedEvenPositiveLimitingRoot s k j) := by
    rw [Complex.normSq_sub]
    have hz : Complex.normSq (sixVertexBethePhase
        (sixVertexFixedEvenPositiveLimitingRoot s k j)) = 1 := by
      rw [Complex.normSq_eq_norm_sq,
        sixVertexBethePhase_norm, one_pow]
    rw [Complex.normSq_one, hz]
    simp [sixVertexBethePhase, Complex.exp_re]
    norm_num
  rw [hden]
  rfl



def sixVertexFixedEvenChargeBetheCandidateNormalized
    (s k : Nat) (c : Real) : Real :=
  if hc : 2 < c then
    sixVertexFixedEvenChargeBetheEigenvalueValue hc s k /
      (c ^ 2 - 2) ^ sixVertexFixedChargeBetheParticleCount (2 * s) k
  else 0



def sixVertexFixedEvenChargeBetheCandidateInfinity (s k : Nat) : Real :=
  2 * ∏ j : Fin (s + k + 1),
    sixVertexFixedEvenPositiveLimitingMNormSq s k j

theorem tendsto_sixVertexFixedEvenChargeBetheCandidateNormalized
    (s k : Nat) :
    Tendsto (sixVertexFixedEvenChargeBetheCandidateNormalized s k) atTop
      (nhds (sixVertexFixedEvenChargeBetheCandidateInfinity s k)) := by
  have hfactors : Tendsto
      (fun c => ∏ j : Fin (s + k + 1), Complex.normSq
        (sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexFixedEvenPositiveBetheRootAt s k j c)) /
          (c ^ 2 - 2 : Real)))
      atTop
      (nhds (∏ j : Fin (s + k + 1),
        sixVertexFixedEvenPositiveLimitingMNormSq s k j)) := by
    exact tendsto_finsetProd Finset.univ fun j _ =>
      tendsto_sixVertexFixedEvenPositiveBetheM_normSq_normalized s k j
  have hprod : Tendsto
      (fun c => 2 * ∏ j : Fin (s + k + 1), Complex.normSq
        (sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexFixedEvenPositiveBetheRootAt s k j c)) /
          (c ^ 2 - 2 : Real)))
      atTop
      (nhds (2 * ∏ j : Fin (s + k + 1),
        sixVertexFixedEvenPositiveLimitingMNormSq s k j)) := by
    exact (tendsto_const_nhds.mul hfactors : _)
  unfold sixVertexFixedEvenChargeBetheCandidateInfinity
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  rw [sixVertexFixedEvenChargeBetheCandidateNormalized, dif_pos hc]
  unfold sixVertexFixedEvenChargeBetheEigenvalueValue
    sixVertexSymmetricBetheEigenvalueValue
  simp_rw [sixVertexFixedEvenPositiveBetheRootAt_eq hc,
    Complex.normSq_div, Complex.normSq_eq_norm_sq]
  have hd : c ^ 2 - 2 ≠ 0 := by nlinarith
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  have hcount : 2 * s + 2 * (k + 1) = 2 * (s + k + 1) := by omega
  rw [hcount, pow_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by nlinarith : 0 < c ^ 2 - 2)]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

end

end StatMech.FrontierD
