/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingFreeEnergy










open Filter Matrix
open scoped Topology BigOperators

namespace StatMech.FrontierA



def quantumIsingBoolTransferEquiv : Bool ≃ Fin 2 where
  toFun b := if b then 0 else 1
  invFun s := s = 0
  left_inv b := by cases b <;> simp
  right_inv s := by fin_cases s <;> simp

@[simp] theorem transferSpin_quantumIsingBoolTransferEquiv (b : Bool) :
    FrontierC.transferSpin (quantumIsingBoolTransferEquiv b) =
      quantumIsingSpinSign b := by
  cases b <;> simp [quantumIsingBoolTransferEquiv]



def quantumIsingConfigTransferEquiv (L : Nat) :
    QuantumIsingChainConfig L ≃ (Fin L → Fin 2) :=
  Equiv.piCongrRight fun _ ↦ quantumIsingBoolTransferEquiv

@[simp] theorem quantumIsingConfigTransferEquiv_apply
    (L : Nat) (sigma : QuantumIsingChainConfig L) (i : Fin L) :
    quantumIsingConfigTransferEquiv L sigma i =
      quantumIsingBoolTransferEquiv (sigma i) := rfl



theorem quantumIsingBoltzmannGenerator_zero_field
    (beta : Real) (L : Nat) :
    quantumIsingBoltzmannGenerator beta 0 L =
      Matrix.diagonal (fun sigma ↦
        ((beta / 4 * quantumIsingChainInteraction L sigma : Real) : Complex)) := by
  classical
  ext sigma tau
  rw [quantumIsingBoltzmannGenerator_apply]
  by_cases hst : sigma = tau
  · subst tau
    simp
  · simp [hst]


theorem quantumIsingQuantumPartition_zero_field_sum
    (beta : Real) (L : Nat) :
    quantumIsingQuantumPartition beta 0 L =
      ∑ sigma : QuantumIsingChainConfig L,
        (Real.exp (beta / 4 * quantumIsingChainInteraction L sigma) : Complex) := by
  classical
  rw [quantumIsingQuantumPartition,
    quantumIsingBoltzmannGenerator_zero_field, Matrix.exp_diagonal,
    Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [Pi.coe_exp]
  rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.ofReal_exp_ℝ_ℝ _).symm



theorem quantumIsingChainInteraction_eq_transfer
    (L : Nat) [NeZero L] (sigma : QuantumIsingChainConfig L) :
    quantumIsingChainInteraction L sigma =
      ∑ i : Fin L,
        FrontierC.transferSpin (quantumIsingConfigTransferEquiv L sigma i) *
          FrontierC.transferSpin
            (quantumIsingConfigTransferEquiv L sigma (i + 1)) := by
  unfold quantumIsingChainInteraction
  apply Finset.sum_congr rfl
  intro i hi
  rw [quantumIsingCyclicSucc_eq_add_one]
  simp



theorem isingRingExponent_configTransfer_zero
    (beta : Real) (L : Nat) [NeZero L]
    (sigma : QuantumIsingChainConfig L) :
    FrontierC.isingRingExponent (beta / 4) 0
        (quantumIsingConfigTransferEquiv L sigma) =
      beta / 4 * quantumIsingChainInteraction L sigma := by
  rw [FrontierC.isingRingExponent, zero_mul, add_zero,
    quantumIsingChainInteraction_eq_transfer]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring



theorem quantumIsingQuantumPartition_zero_field_eq_isingRingZ
    (beta : Real) (L : Nat) [NeZero L] :
    quantumIsingQuantumPartition beta 0 L =
      (FrontierC.isingRingZ L (beta / 4) 0 : Complex) := by
  rw [quantumIsingQuantumPartition_zero_field_sum]
  norm_cast
  rw [FrontierC.isingRingZ]
  rw [← Equiv.sum_comp (quantumIsingConfigTransferEquiv L)
    (fun s : Fin L → Fin 2 ↦
      Real.exp (FrontierC.isingRingExponent (beta / 4) 0 s))]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [isingRingExponent_configTransfer_zero]

theorem quantumIsingQuantumPartition_zero_field_norm
    (beta : Real) (L : Nat) [NeZero L] :
    ‖quantumIsingQuantumPartition beta 0 L‖ =
      FrontierC.isingRingZ L (beta / 4) 0 := by
  rw [quantumIsingQuantumPartition_zero_field_eq_isingRingZ,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (FrontierC.isingRingZ_pos L (beta / 4) 0)]

theorem quantumIsingFiniteFreeEnergy_zero_field_eq_ringPressure
    (beta : Real) (n : Nat) :
    quantumIsingFiniteFreeEnergy beta 0 (n + 1) =
      -(Real.log (FrontierC.isingRingZ (n + 1) (beta / 4) 0) /
          (n + 1 : Real)) / beta := by
  unfold quantumIsingFiniteFreeEnergy
  rw [quantumIsingQuantumPartition_zero_field_norm]
  push_cast
  ring

theorem isingTransferEigenPlus_quarter_zero (beta : Real) :
    FrontierC.isingTransferEigenPlus (beta / 4) 0 =
      2 * Real.cosh (beta / 4) := by
  rw [FrontierC.isingTransferEigenPlus_closed_form]
  simp only [Real.cosh_zero, mul_one, Real.sinh_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, zero_add]
  rw [← Real.exp_half]
  rw [Real.cosh_eq]
  ring_nf

theorem quantumIsingModeLog_zero (beta k : Real) :
    quantumIsingModeLog beta 0 k =
      Real.log (Real.cosh (beta / 4)) := by
  unfold quantumIsingModeLog quantumIsingDispersion
  norm_num

theorem quantumIsingFreeEnergyValue_zero
    (beta : Real) (hbeta : beta ≠ 0) :
    quantumIsingFreeEnergyValue beta 0 =
      -Real.log (2 * Real.cosh (beta / 4)) / beta := by
  unfold quantumIsingFreeEnergyValue
  simp_rw [quantumIsingModeLog_zero]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
    (Real.cosh_pos (beta / 4)).ne']
  field_simp [hbeta, Real.pi_ne_zero]
  ring



theorem quantumIsingFiniteFreeEnergy_tendsto_zero_field
    (beta : Real) (hbeta : 0 < beta) :
    Tendsto (quantumIsingFiniteFreeEnergy beta 0) atTop
      (nhds (quantumIsingFreeEnergyValue beta 0)) := by
  have hp := FrontierC.isingRing_pressure_tendsto (beta / 4) 0
  have hscaled := hp.neg.div_const beta
  rw [isingTransferEigenPlus_quarter_zero,
    ← quantumIsingFreeEnergyValue_zero beta hbeta.ne'] at hscaled
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply hscaled.congr'
  filter_upwards with n
  exact (quantumIsingFiniteFreeEnergy_zero_field_eq_ringPressure beta n).symm



theorem quantumIsingFiniteFreeEnergy_tendsto
    (beta h : Real) (hbeta : 0 < beta) :
    Tendsto (quantumIsingFiniteFreeEnergy beta h) atTop
      (nhds (quantumIsingFreeEnergyValue beta h)) := by
  by_cases hh : h = 0
  · subst h
    exact quantumIsingFiniteFreeEnergy_tendsto_zero_field beta hbeta
  · exact quantumIsingFiniteFreeEnergy_tendsto_of_ne_zero beta h hbeta hh

end StatMech.FrontierA
