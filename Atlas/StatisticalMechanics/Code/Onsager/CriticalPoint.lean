/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace StatMech.Onsager

open Real


noncomputable def ons_gInt (β k₁ k₂ : ℝ) : ℝ :=
  Real.cosh (2*β)^2 - Real.sinh (2*β) * (Real.cos k₁ + Real.cos k₂)


noncomputable def ons_betaC : ℝ := (1/2) * Real.log (1 + Real.sqrt 2)


theorem ons_sq_identity (β : ℝ) :
    Real.cosh (2*β)^2 - 2 * Real.sinh (2*β) = (Real.sinh (2*β) - 1)^2 := by
  have h := Real.cosh_sq_sub_sinh_sq (2*β)
  nlinarith [h]


theorem ons_gInt_zero (β : ℝ) :
    ons_gInt β 0 0 = (Real.sinh (2*β) - 1)^2 := by
  unfold ons_gInt
  rw [Real.cos_zero]
  have h := ons_sq_identity β
  nlinarith [h]


theorem ons_gInt_nonneg_at_zero (β : ℝ) : 0 ≤ ons_gInt β 0 0 := by
  rw [ons_gInt_zero]
  exact sq_nonneg _


theorem ons_gInt_min (β k₁ k₂ : ℝ) (hβ : 0 ≤ β) :
    ons_gInt β 0 0 ≤ ons_gInt β k₁ k₂ := by
  unfold ons_gInt
  have hsinh : 0 ≤ Real.sinh (2*β) := by
    rw [Real.sinh_nonneg_iff]; linarith
  have hc1 : Real.cos k₁ ≤ 1 := Real.cos_le_one k₁
  have hc2 : Real.cos k₂ ≤ 1 := Real.cos_le_one k₂
  rw [Real.cos_zero]
  have : Real.sinh (2*β) * (Real.cos k₁ + Real.cos k₂)
      ≤ Real.sinh (2*β) * (1 + 1) := by
    apply mul_le_mul_of_nonneg_left _ hsinh
    linarith
  linarith


theorem ons_gInt_zero_eq_zero_iff (β : ℝ) :
    ons_gInt β 0 0 = 0 ↔ Real.sinh (2*β) = 1 := by
  rw [ons_gInt_zero, sq_eq_zero_iff, sub_eq_zero]


theorem ons_betaC_sinh : Real.sinh (2 * ons_betaC) = 1 := by
  have h2mul : 2 * ons_betaC = Real.log (1 + Real.sqrt 2) := by
    unfold ons_betaC; ring
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hspos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpos : (0:ℝ) < 1 + Real.sqrt 2 := by linarith
  have hprod : (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = 1 := by nlinarith [hs]
  have hinv : (1 + Real.sqrt 2)⁻¹ = Real.sqrt 2 - 1 :=
    inv_eq_of_mul_eq_one_right hprod
  rw [h2mul, Real.sinh_log hpos, hinv]
  ring


theorem ons_betaC_pos : 0 < ons_betaC := by
  unfold ons_betaC
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlog : 0 < Real.log (1 + Real.sqrt 2) := Real.log_pos (by linarith)
  linarith


theorem ons_betaC_unique (β : ℝ) (hβ : 0 < β) :
    Real.sinh (2*β) = 1 ↔ β = ons_betaC := by
  constructor
  · intro h
    have hc := ons_betaC_sinh
    have heq : Real.sinh (2*β) = Real.sinh (2 * ons_betaC) := by rw [h, hc]
    have := Real.sinh_injective heq
    linarith
  · intro h
    rw [h]
    exact ons_betaC_sinh

end StatMech.Onsager
