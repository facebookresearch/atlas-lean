/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.DefaultableZeroCoupon
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Tests for defaultable zero-coupon bonds

Two states with `ψ = ![2/5, 1/2]` (`D = 9/10`), default in state `0`, `N = 100`,
`R = 1/4`: state-price value `60`, `q_D = 4/9`, plus the full-recovery (`R = 1`,
price `90`) and zero-recovery (`R = 0`, price `50`) edge cases.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Finance.DefaultableZeroCoupon

open _root_.MathlibExt.Probability.Finance.DefaultableZeroCoupon


theorem discountFactor_val :
    riskFreeDiscountFactor (![2/5, 1/2] : Fin 2 → ℝ) = 9 / 10 := by
  unfold riskFreeDiscountFactor
  rw [Fin.sum_univ_two]
  simp
  norm_num

theorem payoff_default_state :
    defaultablePayoff (100 : ℝ) (1/4 : ℝ) (fun ω : Fin 2 => ω = 0) 0 = 25 := by
  unfold defaultablePayoff
  norm_num

theorem payoff_survival_state :
    defaultablePayoff (100 : ℝ) (1/4 : ℝ) (fun ω : Fin 2 => ω = 0) 1 = 100 := by
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  unfold defaultablePayoff
  simp [h10]

theorem statePriceValue_val :
    ∑ ω, (![2/5, 1/2] : Fin 2 → ℝ) ω
      * defaultablePayoff (100 : ℝ) (1/4 : ℝ) (fun ω : Fin 2 => ω = 0) ω = 60 := by
  rw [Fin.sum_univ_two, payoff_default_state, payoff_survival_state]
  simp
  norm_num

theorem defaultProb_val :
    riskNeutralDefaultProb (![2/5, 1/2] : Fin 2 → ℝ) (fun ω : Fin 2 => ω = 0)
      = 4 / 9 := by
  unfold riskNeutralDefaultProb riskFreeDiscountFactor
  have hfilter : Finset.univ.filter (fun ω : Fin 2 => ω = 0) = {0} := by
    ext ω
    simp
  rw [hfilter, Finset.sum_singleton, Fin.sum_univ_two]
  simp
  norm_num

theorem pricingFormula_val :
    riskFreeDiscountFactor (![2/5, 1/2] : Fin 2 → ℝ) * 100
      * (1 - riskNeutralDefaultProb (![2/5, 1/2] : Fin 2 → ℝ)
        (fun ω : Fin 2 => ω = 0) * (1 - 1/4)) = 60 := by
  rw [discountFactor_val, defaultProb_val]
  norm_num

theorem pricingFormula_applies
    (hD : riskFreeDiscountFactor (![2/5, 1/2] : Fin 2 → ℝ) ≠ 0) :
    ∑ ω, (![2/5, 1/2] : Fin 2 → ℝ) ω
      * defaultablePayoff (100 : ℝ) (1/4 : ℝ) (fun ω : Fin 2 => ω = 0) ω
      = riskFreeDiscountFactor (![2/5, 1/2] : Fin 2 → ℝ) * 100
        * (1 - riskNeutralDefaultProb (![2/5, 1/2] : Fin 2 → ℝ)
          (fun ω : Fin 2 => ω = 0) * (1 - 1/4)) :=
  statePriceValue_eq_discountFactor_mul hD

theorem fullRecovery_price :
    ∑ ω, (![2/5, 1/2] : Fin 2 → ℝ) ω
      * defaultablePayoff (100 : ℝ) 1 (fun ω : Fin 2 => ω = 0) ω = 90 := by
  rw [Fin.sum_univ_two]
  have p0 : defaultablePayoff (100 : ℝ) (1 : ℝ) (fun ω : Fin 2 => ω = 0) 0
      = 100 := by
    unfold defaultablePayoff
    norm_num
  have p1 : defaultablePayoff (100 : ℝ) (1 : ℝ) (fun ω : Fin 2 => ω = 0) 1
      = 100 := by
    have h10 : ¬ ((1 : Fin 2) = 0) := by decide
    unfold defaultablePayoff
    simp [h10]
  rw [p0, p1]
  simp
  norm_num

theorem fullRecovery_discount :
    riskFreeDiscountFactor (![2/5, 1/2] : Fin 2 → ℝ) * 100 = 90 := by
  rw [discountFactor_val]
  norm_num

theorem zeroRecovery_price :
    ∑ ω, (![2/5, 1/2] : Fin 2 → ℝ) ω
      * defaultablePayoff (100 : ℝ) 0 (fun ω : Fin 2 => ω = 0) ω = 50 := by
  rw [Fin.sum_univ_two]
  have p0 : defaultablePayoff (100 : ℝ) (0 : ℝ) (fun ω : Fin 2 => ω = 0) 0
      = 0 := by
    unfold defaultablePayoff
    norm_num
  have p1 : defaultablePayoff (100 : ℝ) (0 : ℝ) (fun ω : Fin 2 => ω = 0) 1
      = 100 := by
    have h10 : ¬ ((1 : Fin 2) = 0) := by decide
    unfold defaultablePayoff
    simp [h10]
  rw [p0, p1]
  simp
  norm_num

theorem zeroRecovery_discount :
    riskFreeDiscountFactor (![2/5, 1/2] : Fin 2 → ℝ) * 100
      * (1 - riskNeutralDefaultProb (![2/5, 1/2] : Fin 2 → ℝ)
        (fun ω : Fin 2 => ω = 0)) = 50 := by
  rw [discountFactor_val, defaultProb_val]
  norm_num

end MathlibExtTest.Probability.Finance.DefaultableZeroCoupon
