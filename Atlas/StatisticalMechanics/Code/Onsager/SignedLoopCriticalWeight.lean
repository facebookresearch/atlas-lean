/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.CriticalPoint
import Code.Ising.KramersWannier
import Mathlib.Analysis.SpecialFunctions.Artanh










namespace StatMech.Onsager


noncomputable def ons_signedLoopCriticalWeight : ℝ := Real.sqrt 2 - 1

theorem ons_betaC_eq_selfDualPoint :
    ons_betaC = StatMech.Ising.selfDualPoint := by
  rw [StatMech.Ising.selfDualPoint_eq_log]
  rfl

theorem ons_signedLoopCriticalWeight_pos :
    0 < ons_signedLoopCriticalWeight := by
  unfold ons_signedLoopCriticalWeight
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt0 := Real.sqrt_nonneg 2
  nlinarith

theorem ons_signedLoopCriticalWeight_lt_one :
    ons_signedLoopCriticalWeight < 1 := by
  unfold ons_signedLoopCriticalWeight
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt0 := Real.sqrt_nonneg 2
  nlinarith

private theorem two_mul_ons_betaC :
    2 * ons_betaC = Real.log (1 + Real.sqrt 2) := by
  unfold ons_betaC
  ring



theorem exp_neg_two_ons_betaC :
    Real.exp (-2 * ons_betaC) = ons_signedLoopCriticalWeight := by
  rw [show -2 * ons_betaC = -(2 * ons_betaC) by ring,
    two_mul_ons_betaC, Real.exp_neg]
  have hspos : 0 < 1 + Real.sqrt 2 := by positivity
  rw [Real.exp_log hspos]
  unfold ons_signedLoopCriticalWeight
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : 1 + Real.sqrt 2 ≠ 0 := ne_of_gt hspos
  field_simp [hne]
  nlinarith

private theorem tanh_eq_one_sub_exp_neg_two_div (x : ℝ) :
    Real.tanh x =
      (1 - Real.exp (-2 * x)) / (1 + Real.exp (-2 * x)) := by
  rw [Real.tanh_eq]
  have htwo : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  have hnegTwo : Real.exp (-2 * x) =
      (Real.exp x * Real.exp x)⁻¹ := by
    rw [show -2 * x = -(2 * x) by ring, Real.exp_neg, htwo]
  rw [Real.exp_neg, hnegTwo]
  field_simp [Real.exp_ne_zero]



theorem tanh_ons_betaC :
    Real.tanh ons_betaC = ons_signedLoopCriticalWeight := by
  rw [tanh_eq_one_sub_exp_neg_two_div, exp_neg_two_ons_betaC]
  unfold ons_signedLoopCriticalWeight
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt0 := Real.sqrt_nonneg 2
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hne]
  nlinarith

theorem tanh_lt_signedLoopCriticalWeight {beta : ℝ}
    (hbeta : beta < ons_betaC) :
    Real.tanh beta < ons_signedLoopCriticalWeight := by
  rw [← tanh_ons_betaC]
  have hmemBeta : Real.tanh beta ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨Real.neg_one_lt_tanh beta, Real.tanh_lt_one beta⟩
  have hmemCrit : Real.tanh ons_betaC ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨Real.neg_one_lt_tanh ons_betaC, Real.tanh_lt_one ons_betaC⟩
  rw [← Real.artanh_lt_artanh_iff hmemBeta hmemCrit,
    Real.artanh_tanh, Real.artanh_tanh]
  exact hbeta

theorem tanh_le_signedLoopCriticalWeight {beta : ℝ}
    (hbeta : beta ≤ ons_betaC) :
    Real.tanh beta ≤ ons_signedLoopCriticalWeight := by
  rw [← tanh_ons_betaC]
  have hmemBeta : Real.tanh beta ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨Real.neg_one_lt_tanh beta, Real.tanh_lt_one beta⟩
  have hmemCrit : Real.tanh ons_betaC ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨Real.neg_one_lt_tanh ons_betaC, Real.tanh_lt_one ons_betaC⟩
  rw [← Real.artanh_le_artanh_iff hmemBeta hmemCrit,
    Real.artanh_tanh, Real.artanh_tanh]
  exact hbeta

theorem exp_neg_two_lt_signedLoopCriticalWeight {beta : ℝ}
    (hbeta : ons_betaC < beta) :
    Real.exp (-2 * beta) < ons_signedLoopCriticalWeight := by
  rw [← exp_neg_two_ons_betaC]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem exp_neg_two_le_signedLoopCriticalWeight {beta : ℝ}
    (hbeta : ons_betaC ≤ beta) :
    Real.exp (-2 * beta) ≤ ons_signedLoopCriticalWeight := by
  rw [← exp_neg_two_ons_betaC]
  exact Real.exp_le_exp.mpr (by linarith)


theorem sqrt_two_add_one_mul_signedLoopCriticalWeight :
    (Real.sqrt 2 + 1) * ons_signedLoopCriticalWeight = 1 := by
  unfold ons_signedLoopCriticalWeight
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

theorem signedLoopCriticalWeight_eq_inv_sqrt_two_add_one :
    ons_signedLoopCriticalWeight = (Real.sqrt 2 + 1)⁻¹ := by
  have hpos : 0 < Real.sqrt 2 + 1 := by positivity
  rw [inv_eq_one_div, eq_div_iff hpos.ne']
  rw [mul_comm]
  exact sqrt_two_add_one_mul_signedLoopCriticalWeight

end StatMech.Onsager
