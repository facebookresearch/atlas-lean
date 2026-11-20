/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheAnisotropyRoots
import Code.FrontierD.SixVertexBetheFixedChargeRoots

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexFixedChargeBetheComplementCount (r k : Nat) : Nat :=
  sixVertexFourWidth r k - sixVertexFixedChargeBetheParticleCount r k

@[simp] theorem sixVertexFixedChargeBetheComplementCount_eq (r k : Nat) :
    sixVertexFixedChargeBetheComplementCount r k = 3 * r + 2 * (k + 1) := by
  unfold sixVertexFixedChargeBetheComplementCount sixVertexFourWidth
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  omega

theorem sixVertexFixedChargeBetheComplementCount_pos (r k : Nat) :
    0 < sixVertexFixedChargeBetheComplementCount r k := by
  rw [sixVertexFixedChargeBetheComplementCount_eq]
  omega


def sixVertexFixedChargeBetheRootAt (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) (c : Real) : Real :=
  if hc : 2 < c then sixVertexFixedChargeBetheRoots hc r k j else 0

theorem sixVertexFixedChargeBetheRootAt_eq
    {c : Real} (hc : 2 < c) (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeBetheRootAt r k j c =
      sixVertexFixedChargeBetheRoots hc r k j := by
  simp only [sixVertexFixedChargeBetheRootAt, dif_pos hc]




def sixVertexFixedChargeLimitingRoot (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) : Real :=
  (2 * Real.pi * sixVertexCentralQuantumNumber j) /
    (sixVertexFixedChargeBetheComplementCount r k : Real)


def sixVertexFixedChargeLimitingPhase (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) : Complex :=
  sixVertexBethePhase (sixVertexFixedChargeLimitingRoot r k j)

theorem sixVertexFixedChargeLimitingRoot_mem_Ioo (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingRoot r k j ∈ Set.Ioo (-Real.pi) Real.pi := by
  let n := sixVertexFixedChargeBetheParticleCount r k
  let m := sixVertexFixedChargeBetheComplementCount r k
  have hn : 0 < n := sixVertexFixedChargeBetheParticleCount_pos r k
  have hm : 0 < m := sixVertexFixedChargeBetheComplementCount_pos r k
  have hnm : n <= m := by
    dsimp [n, m]
    rw [sixVertexFixedChargeBetheParticleCount_eq,
      sixVertexFixedChargeBetheComplementCount_eq]
    omega
  have hquantum :
      -(m : Real) < 2 * sixVertexCentralQuantumNumber j ∧
        2 * sixVertexCentralQuantumNumber j < (m : Real) := by
    rw [sixVertexCentralQuantumNumber_eq]
    have hj0 : (0 : Real) <= j.val := by positivity
    have hjlt : (j.val : Real) < n := by exact_mod_cast j.isLt
    have hjstep : (j.val : Real) + 1 <= n := by
      exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
    have hnlem : (n : Real) <= m := by exact_mod_cast hnm
    constructor <;> dsimp [n, m] at hjlt hnlem ⊢ <;> nlinarith
  change -Real.pi <
      (2 * Real.pi * sixVertexCentralQuantumNumber j) / (m : Real) ∧
    (2 * Real.pi * sixVertexCentralQuantumNumber j) / (m : Real) < Real.pi
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  constructor
  · rw [lt_div_iff₀ hmReal]
    have := mul_lt_mul_of_pos_left hquantum.1 Real.pi_pos
    nlinarith
  · rw [div_lt_iff₀ hmReal]
    have := mul_lt_mul_of_pos_left hquantum.2 Real.pi_pos
    nlinarith



theorem sixVertexFixedChargeLimitingPhase_injective (r k : Nat) :
    Function.Injective (sixVertexFixedChargeLimitingPhase r k) := by
  intro i j hij
  have hroot := sixVertexBethePhase_injective_on_Ioo
    (sixVertexFixedChargeLimitingRoot_mem_Ioo r k i)
    (sixVertexFixedChargeLimitingRoot_mem_Ioo r k j) hij
  have hm : (0 : Real) <
      (sixVertexFixedChargeBetheComplementCount r k : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheComplementCount_pos r k
  have hquantum : sixVertexCentralQuantumNumber i =
      sixVertexCentralQuantumNumber j := by
    unfold sixVertexFixedChargeLimitingRoot at hroot
    field_simp [hm.ne', Real.pi_ne_zero] at hroot
    linarith
  exact (strictMono_sixVertexCentralQuantumNumber
    (sixVertexFixedChargeBetheParticleCount r k)).injective hquantum

private theorem sixVertexFixedChargeBetheRootAt_equation
    {c : Real} (hc : 2 < c) (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    (sixVertexFourWidth r k : Real) *
        sixVertexFixedChargeBetheRootAt r k j c =
      2 * Real.pi * sixVertexCentralQuantumNumber j -
        ∑ l, sixVertexTheta c
          (sixVertexFixedChargeBetheRootAt r k j c)
          (sixVertexFixedChargeBetheRootAt r k l c) := by
  simpa only [sixVertexFixedChargeBetheRootAt_eq hc] using
    sixVertexFixedChargeBetheRoots_is_solution hc r k j

private theorem sixVertexFixedChargeBetheRootAt_sum_eq_zero
    {c : Real} (hc : 2 < c) (r k : Nat) :
    ∑ l, sixVertexFixedChargeBetheRootAt r k l c = 0 := by
  simpa only [sixVertexFixedChargeBetheRootAt_eq hc] using
    sixVertexFixedChargeBetheRoots_sum_eq_zero hc r k

private def sixVertexFixedChargeBetheRootError (r k : Nat)
    (j l : Fin (sixVertexFixedChargeBetheParticleCount r k))
    (c : Real) : Real :=
  sixVertexTheta c
      (sixVertexFixedChargeBetheRootAt r k j c)
      (sixVertexFixedChargeBetheRootAt r k l c) -
    (sixVertexFixedChargeBetheRootAt r k l c -
      sixVertexFixedChargeBetheRootAt r k j c)

private theorem tendsto_sixVertexFixedChargeBetheRootError
    (r k : Nat) (j l : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto (sixVertexFixedChargeBetheRootError r k j l) atTop (nhds 0) := by
  exact tendsto_sixVertexTheta_sub_linear_atTop
    (sixVertexFixedChargeBetheRootAt r k j)
    (sixVertexFixedChargeBetheRootAt r k l)

private theorem tendsto_sixVertexFixedChargeBetheRootError_sum
    (r k : Nat) (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto (fun c => ∑ l, sixVertexFixedChargeBetheRootError r k j l c)
      atTop (nhds 0) := by
  simpa using tendsto_finsetSum Finset.univ
    (fun l _ => tendsto_sixVertexFixedChargeBetheRootError r k j l)

private theorem sixVertexFixedChargeBetheRootAt_eq_quantum_sub_error
    {c : Real} (hc : 2 < c) (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeBetheRootAt r k j c =
      (2 * Real.pi * sixVertexCentralQuantumNumber j -
          ∑ l, sixVertexFixedChargeBetheRootError r k j l c) /
        (sixVertexFixedChargeBetheComplementCount r k : Real) := by
  have heq := sixVertexFixedChargeBetheRootAt_equation hc r k j
  have hsum := sixVertexFixedChargeBetheRootAt_sum_eq_zero hc r k
  have hm : (0 : Real) <
      (sixVertexFixedChargeBetheComplementCount r k : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheComplementCount_pos r k
  have herr :
      (∑ l, sixVertexFixedChargeBetheRootError r k j l c) =
        (∑ l, sixVertexTheta c
          (sixVertexFixedChargeBetheRootAt r k j c)
          (sixVertexFixedChargeBetheRootAt r k l c)) +
        (sixVertexFixedChargeBetheParticleCount r k : Real) *
          sixVertexFixedChargeBetheRootAt r k j c := by
    unfold sixVertexFixedChargeBetheRootError
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hwidth :
      (sixVertexFourWidth r k : Real) =
        (sixVertexFixedChargeBetheComplementCount r k : Real) +
          (sixVertexFixedChargeBetheParticleCount r k : Real) := by
    rw [sixVertexFixedChargeBetheComplementCount_eq,
      sixVertexFixedChargeBetheParticleCount_eq, sixVertexFourWidth]
    push_cast
    ring
  rw [herr, eq_div_iff hm.ne']
  rw [hwidth] at heq
  linarith [heq]




theorem tendsto_sixVertexFixedChargeBetheRootAt (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto (sixVertexFixedChargeBetheRootAt r k j) atTop
      (nhds (sixVertexFixedChargeLimitingRoot r k j)) := by
  have herror := tendsto_sixVertexFixedChargeBetheRootError_sum r k j
  have hformula : (fun c => sixVertexFixedChargeBetheRootAt r k j c) =ᶠ[atTop]
      fun c =>
        (2 * Real.pi * sixVertexCentralQuantumNumber j -
            ∑ l, sixVertexFixedChargeBetheRootError r k j l c) /
          (sixVertexFixedChargeBetheComplementCount r k : Real) := by
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    exact sixVertexFixedChargeBetheRootAt_eq_quantum_sub_error hc r k j
  apply Tendsto.congr' hformula.symm
  simpa [sixVertexFixedChargeLimitingRoot] using
    (tendsto_const_nhds.sub herror).div_const
      (sixVertexFixedChargeBetheComplementCount r k : Real)



theorem tendsto_sixVertexFixedChargeBethePhaseAt (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto
      (fun c => sixVertexBethePhase
        (sixVertexFixedChargeBetheRootAt r k j c)) atTop
      (nhds (sixVertexFixedChargeLimitingPhase r k j)) := by
  have hcontinuous : Continuous (fun p : Real => sixVertexBethePhase p) := by
    unfold sixVertexBethePhase
    fun_prop
  exact hcontinuous.continuousAt.tendsto.comp
    (tendsto_sixVertexFixedChargeBetheRootAt r k j)

end

end StatMech.FrontierD
