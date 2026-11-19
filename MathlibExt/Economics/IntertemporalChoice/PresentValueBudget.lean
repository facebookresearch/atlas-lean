/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
public import MathlibExt.Economics.IntertemporalChoice.EulerEquation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The two-period present-value budget constraint

A household consumes `c 0`, `c 1` out of incomes `y 0`, `y 1` and holds the asset `a`
(saving if positive, borrowing if negative): `c 0 + a = y 0` and `c 1 = (1 + r) a + y 1`.
Eliminating `a` gives the present-value budget constraint, stated with the FI01 present
value over the dates `0, 1`.

## Main results

* `MathlibExt.Economics.IntertemporalChoice.exists_asset_iff_presentValue_eq`: some asset
  holding finances the plan iff consumption and income have equal present values.
* `MathlibExt.Economics.IntertemporalChoice.presentValue_budget_iff`: the scalar budget
  `c₀ + c₁ / (1 + r) = y₀ + y₁ / (1 + r)` is the MA04.T02 budget line
  `c₁ = secondPeriodConsumption r y₀ y₁ c₀`.

Only `1 + r ≠ 0` is assumed; no borrowing limit is part of the budget identity.

## References

MIT 14.05 Intermediate Macroeconomics (consumption). Atlas roadmap target MA04.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.IntertemporalChoice

open MathlibExt.Economics.Finance

/-- Eliminating the asset holding: a two-date consumption plan `c` is financed by
some asset holding `a` (date-0 budget `c 0 + a = y 0`, date-1 budget
`c 1 = (1 + r) a + y 1`) exactly when the present value of consumption equals the
present value of income at the rate `r` (Atlas roadmap MA04.T01). -/
theorem exists_asset_iff_presentValue_eq {r : ℝ} {c y : ℕ → ℝ} (h1r : 1 + r ≠ 0) :
    (∃ a : ℝ, c 0 + a = y 0 ∧ c 1 = (1 + r) * a + y 1) ↔
      presentValue (discountFactor r) (Finset.range 2) c =
        presentValue (discountFactor r) (Finset.range 2) y := by
  -- Expand the two-date present value with `Finset.sum_range_succ`.
  have hPV : ∀ f : ℕ → ℝ, presentValue (discountFactor r) (Finset.range 2) f
      = f 0 + ((1 + r) ^ 1)⁻¹ * f 1 := by
    intro f
    unfold presentValue discountFactor
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp
  rw [hPV, hPV, pow_one]
  constructor
  · rintro ⟨a, h0, h1⟩
    have hdiv : ∀ x : ℝ, (1 + r)⁻¹ * x = x / (1 + r) := fun x => by rw [div_eq_mul_inv, mul_comm]
    rw [hdiv, hdiv]
    -- Clear denominators with `mul_div_cancel₀`, then cancel the nonzero factor.
    have hL : (1 + r) * (c 0 + c 1 / (1 + r)) = (1 + r) * c 0 + c 1 := by
      rw [mul_add, mul_div_cancel₀ (c 1) h1r]
    have hR : (1 + r) * (y 0 + y 1 / (1 + r)) = (1 + r) * y 0 + y 1 := by
      rw [mul_add, mul_div_cancel₀ (y 1) h1r]
    have hcore : (1 + r) * c 0 + c 1 = (1 + r) * y 0 + y 1 := by
      linear_combination (1 + r) * h0 + h1
    have hmulgoal : (1 + r) * (c 0 + c 1 / (1 + r)) = (1 + r) * (y 0 + y 1 / (1 + r)) := by
      linear_combination hL - hR + hcore
    exact mul_left_cancel₀ h1r hmulgoal
  · intro h
    refine ⟨y 0 - c 0, by ring, ?_⟩
    have hdiv : ∀ x : ℝ, (1 + r)⁻¹ * x = x / (1 + r) := fun x => by rw [div_eq_mul_inv, mul_comm]
    rw [hdiv, hdiv] at h
    have hmul := congrArg (fun x => (1 + r) * x) h
    rw [mul_add, mul_add, mul_div_cancel₀ (c 1) h1r, mul_div_cancel₀ (y 1) h1r] at hmul
    linear_combination hmul

/-- The two-period present-value budget `c₀ + c₁ / (1 + r) = y₀ + y₁ / (1 + r)` is the
binding budget line `c₁ = secondPeriodConsumption r y₀ y₁ c₀` of MA04.T02. -/
theorem presentValue_budget_iff {r y₀ y₁ c₀ c₁ : ℝ} (h1r : 1 + r ≠ 0) :
    c₀ + c₁ / (1 + r) = y₀ + y₁ / (1 + r) ↔ c₁ = secondPeriodConsumption r y₀ y₁ c₀ := by
  unfold secondPeriodConsumption
  constructor
  · intro h
    have hmul := congrArg (fun x => (1 + r) * x) h
    rw [mul_add, mul_add, mul_div_cancel₀ c₁ h1r, mul_div_cancel₀ y₁ h1r] at hmul
    linear_combination hmul
  · intro h
    have hdiv := congrArg (fun x => x / (1 + r)) h
    rw [add_div, mul_div_assoc, mul_div_cancel₀ (y₀ - c₀) h1r] at hdiv
    linear_combination hdiv

end MathlibExt.Economics.IntertemporalChoice
