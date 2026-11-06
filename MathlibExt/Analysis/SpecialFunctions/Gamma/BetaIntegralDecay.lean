/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Decay of `∫₀¹ rᵐ (1 - r)^β dr` in `m`

For `m ≥ 1` and `β ≥ 0`,
`∫₀¹ rᵐ (1 - r)^β dr ≤ Γ(β + 1) · m^{-(β + 1)}`
(`intervalIntegral_pow_mul_one_sub_rpow_le`). With `Γ(β + 1) ≤ 2` for `0 ≤ β ≤ 2`
(`Real.Gamma_add_one_le_two`) this gives the bound `100 m^{-1-β}` of Lemma 3 in
Chapter 1 (Brownian Motion) of the FourierAnalysis notes
(`intervalIntegral_pow_mul_one_sub_rpow_le_hundred`).

Code-derived port of `BetaIntegralBound.beta_integral_bound` and its helper
`Gamma_succ_le_two` from `v1/Atlas/FourierAnalysis/code/BrownianMotion.lean` at
commit `6191bf1ba03d204784385ef5be2472be88035b93`, lines 124–219, restated on the
interval integral itself instead of the archived `R_beta` wrapper and with the
sharp Gamma bound exposed. The archived formalization and its original
license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
This records equivalence to the archived Lean statement, not verification
against the printed textbook.
-/

set_option autoImplicit false

open Set MeasureTheory intervalIntegral

namespace Real

/-- `Γ(β + 1) ≤ 2` for `0 ≤ β ≤ 2`, by log-convexity of `Γ` between `Γ(1) = 1` and
`Γ(3) = 2`. -/
public theorem Gamma_add_one_le_two {β : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) :
    Gamma (β + 1) ≤ 2 := by
  have hG1 : Gamma 1 = 1 := Gamma_one
  have hG3 : Gamma 3 = 2 := by
    have h := Gamma_nat_eq_factorial 2
    push_cast at h
    convert h using 1 <;> norm_num [Nat.factorial]
  rcases hβ0.eq_or_lt with rfl | hβ_pos
  · simp [hG1]
  rcases hβ2.eq_or_lt with rfl | hβ_lt2
  · norm_num [hG3]
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma one_pos
    (by norm_num : (0 : ℝ) < 3) (by linarith : 0 < 1 - β / 2) (by linarith : 0 < β / 2)
    (by ring : (1 - β / 2) + β / 2 = 1)
  rw [show (1 - β / 2) * 1 + β / 2 * 3 = β + 1 by ring, hG1, hG3, one_rpow, one_mul] at h
  calc Gamma (β + 1) ≤ (2 : ℝ) ^ (β / 2) := h
    _ ≤ (2 : ℝ) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 := rpow_one 2

end Real

/-- For `m ≥ 1` and `β ≥ 0`, `∫₀¹ rᵐ (1 - r)^β dr ≤ Γ(β + 1) · m^{-(β + 1)}`. -/
public theorem intervalIntegral_pow_mul_one_sub_rpow_le (m : ℕ) (hm : 1 ≤ m) {β : ℝ}
    (hβ0 : 0 ≤ β) :
    ∫ r in (0 : ℝ)..1, r ^ m * (1 - r) ^ β ≤ (m : ℝ) ^ (-(β + 1)) * Real.Gamma (β + 1) := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hrpow : ContinuousOn (fun r : ℝ => (1 - r) ^ β) (Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).rpow_const fun _ _ => Or.inr hβ0
  have hint_f : IntervalIntegrable (fun r : ℝ => r ^ m * (1 - r) ^ β) volume 0 1 :=
    ((continuous_pow m).continuousOn.mul hrpow).intervalIntegrable_of_Icc zero_le_one
  have hint_g : IntervalIntegrable
      (fun r : ℝ => Real.exp (-(m * (1 - r))) * (1 - r) ^ β) volume 0 1 :=
    ((by fun_prop : Continuous fun r : ℝ => Real.exp (-(m * (1 - r)))).continuousOn.mul
      hrpow).intervalIntegrable_of_Icc zero_le_one
  -- `r ≤ e^{-(1 - r)}`, so `rᵐ ≤ e^{-m(1 - r)}` on `[0, 1]`.
  have step1 : ∫ r in (0 : ℝ)..1, r ^ m * (1 - r) ^ β ≤
      ∫ r in (0 : ℝ)..1, Real.exp (-(m * (1 - r))) * (1 - r) ^ β := by
    refine integral_mono_on zero_le_one hint_f hint_g fun r hr => ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith [hr.2]) _)
    calc r ^ m ≤ Real.exp (-(1 - r)) ^ m :=
          pow_le_pow_left₀ hr.1 (by linarith [Real.add_one_le_exp (-(1 - r))]) m
      _ = Real.exp (-(m * (1 - r))) := by rw [← Real.exp_nat_mul]; ring_nf
  have step2 : ∫ r in (0 : ℝ)..1, Real.exp (-(m * (1 - r))) * (1 - r) ^ β =
      ∫ u in (0 : ℝ)..1, Real.exp (-(m * u)) * u ^ β := by
    simpa using integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun x : ℝ => Real.exp (-(m * x)) * x ^ β) 1
  -- Extend to `(0, ∞)`, where the integral is a Gamma function.
  have step3 : ∫ u in (0 : ℝ)..1, Real.exp (-(m * u)) * u ^ β ≤
      ∫ u in Ioi (0 : ℝ), u ^ β * Real.exp (-(m * u)) := by
    rw [integral_of_le zero_le_one]
    simp_rw [mul_comm (Real.exp _)]
    refine setIntegral_mono_set ?_ ?_ Ioc_subset_Ioi_self.eventuallyLE
    · simpa only [neg_mul, Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < β) one_pos hm_pos
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  have step4 : ∫ u in Ioi (0 : ℝ), u ^ β * Real.exp (-(m * u)) =
      (m : ℝ) ^ (-(β + 1)) * Real.Gamma (β + 1) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow one_pos (by linarith : -1 < β) hm_pos
    simp only [Real.rpow_one, div_one, neg_mul] at h
    rw [h]
    ring_nf
  calc _ ≤ _ := step1
    _ = _ := step2
    _ ≤ _ := step3
    _ = _ := step4

/-- **Lemma 3** (Chapter 1, Brownian Motion): for `m ≥ 1` and `0 ≤ β ≤ 2`,
`∫₀¹ rᵐ (1 - r)^β dr ≤ 100 m^{-1-β}`. -/
public theorem intervalIntegral_pow_mul_one_sub_rpow_le_hundred (m : ℕ) (hm : 1 ≤ m) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) :
    ∫ r in (0 : ℝ)..1, r ^ m * (1 - r) ^ β ≤ 100 * (m : ℝ) ^ (-(1 + β)) := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow : 0 ≤ (m : ℝ) ^ (-(β + 1)) := Real.rpow_nonneg hm_pos.le _
  calc _ ≤ (m : ℝ) ^ (-(β + 1)) * Real.Gamma (β + 1) :=
        intervalIntegral_pow_mul_one_sub_rpow_le m hm hβ0
    _ ≤ (m : ℝ) ^ (-(β + 1)) * 100 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.Gamma_add_one_le_two hβ0 hβ2]) hpow
    _ = 100 * (m : ℝ) ^ (-(1 + β)) := by rw [add_comm β 1, mul_comm]
