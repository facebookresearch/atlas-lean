/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace Complex

open Asymptotics Filter

/-- **Absorbing constants into the exponent gap.** For every real $C > 0$ there is a real $U > 1$
such that for all reals $\mu$ and $A$ with $U \le \mu \le A$ and
$A \le C \mu \bigl(1 + (\log A)^{81/128}\bigr)$, we have $A \le \mu (\log \mu)^{2/3}$.

The gap $2/3 - 81/128 > 0$ between the exponents absorbs the constant $C$ of the corrected
Rosenbloom estimate once the maximum term $\mu$ is large. -/
theorem eventually_absorb_corrected_wiman_exponent
    (C : ℝ) (hC : 0 < C) :
    ∃ U : ℝ, 1 < U ∧ ∀ μ A : ℝ,
      U ≤ μ → μ ≤ A →
      A ≤ C * μ * (1 + Real.log A ^ (81 / 128 : ℝ)) →
      A ≤ μ * Real.log μ ^ (2 / 3 : ℝ) := by
  let α : ℝ := 81 / 128
  let β : ℝ := 2 / 3
  let δ : ℝ := β - α
  have hα : 0 < α := by norm_num [α]
  have hβ : 0 < β := by norm_num [β]
  have hδ : 0 < δ := by norm_num [δ, β, α]
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hconst :
      (fun _ : ℝ ↦ (1 : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) := by
    exact isLittleO_const_left.2 <| Or.inr <|
      tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hhalf)
  have hlog :
      (fun x : ℝ ↦ Real.log x ^ α) =o[atTop] (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop α hhalf
  have hsmall := (hconst.add hlog).const_mul_left C
  have hbootstrap :
      ∀ᶠ x : ℝ in atTop,
        C * (1 + Real.log x ^ α) ≤ x ^ (1 / 2 : ℝ) := by
    filter_upwards [hsmall.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with x hx hxone
    rw [Real.norm_of_nonneg
          (mul_nonneg hC.le (add_nonneg zero_le_one
            (Real.rpow_nonneg (Real.log_nonneg hxone) α))),
        Real.norm_of_nonneg
          (Real.rpow_nonneg (zero_le_one.trans hxone) (1 / 2 : ℝ))] at hx
    exact hx
  let K : ℝ := C * (1 + (2 : ℝ) ^ α)
  have hKlog : ∀ᶠ x : ℝ in atTop, K ≤ Real.log x ^ δ :=
    ((tendsto_rpow_atTop hδ).comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop K)
  have hrequirements :
      ∀ᶠ x : ℝ in atTop,
        1 < x ∧ 1 ≤ Real.log x ∧
          C * (1 + Real.log x ^ α) ≤ x ^ (1 / 2 : ℝ) ∧
          K ≤ Real.log x ^ δ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      hbootstrap, hKlog] with x hx hlogx hbootx hKx
    exact ⟨hx, hlogx, hbootx, hKx⟩
  rcases (eventually_atTop.1 hrequirements) with ⟨U₀, hU₀⟩
  refine ⟨max 2 U₀, lt_of_lt_of_le (by norm_num) (le_max_left 2 U₀), ?_⟩
  intro μ A hUμ hμA hbound
  have hthresholdμ : U₀ ≤ μ := (le_max_right 2 U₀).trans hUμ
  have hthresholdA : U₀ ≤ A := hthresholdμ.trans hμA
  rcases hU₀ μ hthresholdμ with ⟨hμone, hlogμone, _hbootμ, hKμ⟩
  rcases hU₀ A hthresholdA with ⟨hAone, _hlogAone, hbootA, _hKA⟩
  have hμpos : 0 < μ := zero_lt_one.trans hμone
  have hApos : 0 < A := zero_lt_one.trans hAone
  have hAhalf : A ≤ μ * A ^ (1 / 2 : ℝ) := by
    calc
      A ≤ C * μ * (1 + Real.log A ^ α) := by simpa [α] using hbound
      _ = μ * (C * (1 + Real.log A ^ α)) := by ring
      _ ≤ μ * A ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hbootA hμpos.le
  have hAfactor :
      A = A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hApos]
    norm_num
  have hhalfpos : 0 < A ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hApos _
  have hhalf_le : A ^ (1 / 2 : ℝ) ≤ μ := by
    exact le_of_mul_le_mul_right (by
      calc
        A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A := hAfactor.symm
        _ ≤ μ * A ^ (1 / 2 : ℝ) := hAhalf) hhalfpos
  have hA_le_sq : A ≤ μ ^ 2 := by
    rw [hAfactor, pow_two]
    exact mul_le_mul hhalf_le hhalf_le
      (Real.rpow_nonneg hApos.le (1 / 2 : ℝ)) hμpos.le
  have hlogA_le : Real.log A ≤ 2 * Real.log μ := by
    calc
      Real.log A ≤ Real.log (μ ^ 2) := Real.log_le_log hApos hA_le_sq
      _ = 2 * Real.log μ := by norm_num [Real.log_pow]
  have hlogpow_le : Real.log A ^ α ≤ (2 * Real.log μ) ^ α :=
    Real.rpow_le_rpow (Real.log_nonneg hAone.le) hlogA_le hα.le
  have hlogμpos : 0 < Real.log μ := zero_lt_one.trans_le hlogμone
  have hlogμpow : 1 ≤ Real.log μ ^ α := Real.one_le_rpow hlogμone hα.le
  have hinside :
      1 + (2 : ℝ) ^ α * Real.log μ ^ α ≤
        (1 + (2 : ℝ) ^ α) * Real.log μ ^ α := by
    nlinarith
  have hcoefficient :
      C * (1 + (2 * Real.log μ) ^ α) ≤ Real.log μ ^ β := by
    calc
      C * (1 + (2 * Real.log μ) ^ α) =
          C * (1 + (2 : ℝ) ^ α * Real.log μ ^ α) := by
            rw [Real.mul_rpow (by norm_num) hlogμpos.le]
      _ ≤ C * ((1 + (2 : ℝ) ^ α) * Real.log μ ^ α) :=
        mul_le_mul_of_nonneg_left hinside hC.le
      _ = K * Real.log μ ^ α := by simp only [K, mul_assoc]
      _ ≤ Real.log μ ^ δ * Real.log μ ^ α :=
        mul_le_mul_of_nonneg_right hKμ (Real.rpow_nonneg hlogμpos.le α)
      _ = Real.log μ ^ β := by
        rw [← Real.rpow_add hlogμpos]
        congr 1
        norm_num [δ, β, α]
  calc
    A ≤ C * μ * (1 + Real.log A ^ α) := by simpa [α] using hbound
    _ ≤ C * μ * (1 + (2 * Real.log μ) ^ α) := by
      gcongr
    _ = μ * (C * (1 + (2 * Real.log μ) ^ α)) := by ring
    _ ≤ μ * Real.log μ ^ β := mul_le_mul_of_nonneg_left hcoefficient hμpos.le
    _ = μ * Real.log μ ^ (2 / 3 : ℝ) := by rw [show β = (2 / 3 : ℝ) by norm_num [β]]

end Complex
