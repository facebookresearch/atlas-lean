/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Finance.PortfolioReturn
public import Domains.Economics.Finance.Returns

import MathlibExt.Analysis.ScalarCalculus
import Mathlib.Tactic

@[expose] public section


/-!
# Percentage change and log change of a positive quantity

A quantity measured twice in one unit, with base value `x₀` and later value `x₁` (a population,
a price index, a price), has the percentage change `assetReturn x₀ x₁ = (x₁ - x₀) / x₀`, written
as a fraction (a 25% increase is `1 / 4`), the growth factor `grossReturn x₀ x₁ = x₁ / x₀`, and
the log change `priceLogReturn x₀ x₁ = Real.log (x₁ / x₀)`. These three definitions already
exist in `MathlibExt.Economics.Finance.PortfolioReturn` and `MathlibExt.Economics.Finance.Returns`;
this file relates them and defines nothing new.

For a positive base and a positive later value:

* the growth factor is one plus the percentage change, and the later value is the base times
  that factor; a change is above `-100%` exactly when the later value stays positive;
* percentage changes compound multiplicatively over two steps, while log changes add
  (`MathlibExt.Economics.Finance.Returns.priceLogReturn_add`);
* the log change is the difference of logarithms and, exactly, the logarithm of one plus the
  percentage change; conversely the percentage change is `exp` of the log change minus one;
* the percentage change is only a first-order approximation of the log change: the log change
  never exceeds the percentage change, is strictly smaller unless the quantity is unchanged,
  and for changes of at most 50% in absolute value differs from it by at most the square of the
  percentage change;
* both measures are unit-free: a common change of units of `x₀` and `x₁` leaves them unchanged.
  Values recorded in different units must be converted before either measure is formed.

Lean's division and logarithm are total (`x / 0 = 0`, `Real.log 0 = 0`,
`Real.log x = Real.log |x|`). These conventions are not data-validity assumptions. A zero base
gives the junk percentage change `0`, which reads as "no change"; a later value of zero (a
change of exactly `-100%`) gives the junk log change `0`; a negative later value gives the log
change of its absolute value. Each statement below states the nonzero or positive hypotheses its
reading needs. The exact identity `priceLogReturn_eq_log_one_add_assetReturn` holds for all real
arguments, because at a zero base both sides are the junk value `0`; it is a log change only on
positive values.

These are identities and inequalities between numbers computed from two fixed values. They
carry no sampling, statistical or causal claim.

## Main results

* `grossReturn_eq_one_add_assetReturn`, `mul_one_add_assetReturn`: growth factor and level.
* `neg_one_lt_assetReturn_iff`: changes above `-100%` keep a positive base positive.
* `one_add_assetReturn_eq_mul`: percentage changes compound.
* `priceLogReturn_eq_log_sub_log`, `priceLogReturn_eq_log_one_add_assetReturn`,
  `assetReturn_eq_exp_priceLogReturn_sub_one`: exact conversions.
* `priceLogReturn_le_assetReturn`, `priceLogReturn_lt_assetReturn`,
  `abs_priceLogReturn_sub_assetReturn_le`: the first-order approximation and its error.
* `assetReturn_mul_mul`: invariance under a common change of units.

## References

* J. M. Wooldridge, *Introductory Econometrics: A Modern Approach*, Appendix A (the natural
  logarithm and the approximation of a proportionate change by a log difference).
* S. H. Preston, P. Heuveline and M. Guillot, *Demography: Measuring and Modeling Population
  Processes*, Blackwell (2001), Chapter 1 (growth rates).
-/

namespace MathlibExt.Economics.Finance.PercentAndLogChange

open MathlibExt.Economics.Finance.Returns MathlibExt.Economics.Finance.PortfolioReturn

/-- **Growth factor and percentage change.** For a nonzero base, the growth factor `x₁ / x₀` is
one plus the percentage change `(x₁ - x₀) / x₀`. At a zero base the two sides are the junk
values `0` and `1`. -/
theorem grossReturn_eq_one_add_assetReturn {x₀ : ℝ} (x₁ : ℝ) (h₀ : x₀ ≠ 0) :
    grossReturn x₀ x₁ = 1 + assetReturn x₀ x₁ := by
  simp only [grossReturn, assetReturn]
  field_simp
  ring

/-- **Level identity.** For a nonzero base, the later value is the base times one plus the
percentage change. -/
theorem mul_one_add_assetReturn {x₀ : ℝ} (x₁ : ℝ) (h₀ : x₀ ≠ 0) :
    x₀ * (1 + assetReturn x₀ x₁) = x₁ := by
  simp only [assetReturn]
  field_simp
  ring

/-- **Changes above `-100%`.** For a positive base, the percentage change exceeds `-1` if and
only if the later value is positive. A change of exactly `-1` reaches zero, and a smaller one
gives a negative value. -/
theorem neg_one_lt_assetReturn_iff {x₀ : ℝ} (x₁ : ℝ) (h₀ : 0 < x₀) :
    -1 < assetReturn x₀ x₁ ↔ 0 < x₁ := by
  simp only [assetReturn]
  rw [lt_div_iff₀ h₀]
  constructor <;> intro h <;> linarith

/-- **Percentage changes compound.** Over two steps `x₀ → x₁ → x₂` with nonzero `x₀` and `x₁`,
one plus the overall change is the product of one plus the step changes. The overall change is
therefore the sum of the step changes plus their product, not their sum. -/
theorem one_add_assetReturn_eq_mul {x₀ x₁ : ℝ} (x₂ : ℝ) (h₀ : x₀ ≠ 0) (h₁ : x₁ ≠ 0) :
    1 + assetReturn x₀ x₂ = (1 + assetReturn x₀ x₁) * (1 + assetReturn x₁ x₂) := by
  simp only [assetReturn]
  field_simp
  ring

/-- **Log change as a difference of logarithms.** For nonzero values the log change is
`log x₁ - log x₀`; it is a log change of a quantity when both values are positive (for negative
values Lean reads both logarithms through absolute values). -/
theorem priceLogReturn_eq_log_sub_log {x₀ x₁ : ℝ} (h₀ : x₀ ≠ 0) (h₁ : x₁ ≠ 0) :
    priceLogReturn x₀ x₁ = Real.log x₁ - Real.log x₀ := by
  simp only [priceLogReturn, logReturn, grossReturn]
  exact Real.log_div h₁ h₀

/-- **Exact log change from the percentage change.** The log change is the logarithm of one plus
the percentage change. This holds for all real arguments: at a zero base both sides are the junk
value `0`. It is a log change only for positive `x₀` and `x₁`. -/
theorem priceLogReturn_eq_log_one_add_assetReturn (x₀ x₁ : ℝ) :
    priceLogReturn x₀ x₁ = Real.log (1 + assetReturn x₀ x₁) := by
  by_cases h₀ : x₀ = 0
  · simp [priceLogReturn, logReturn, grossReturn, assetReturn, h₀]
  · have h₀' : x₀ ≠ 0 := h₀
    have h : (1 : ℝ) + assetReturn x₀ x₁ = x₁ / x₀ := by
      simp only [assetReturn]
      field_simp
      ring
    simp only [priceLogReturn, logReturn, grossReturn]
    rw [h]

/-- **Percentage change from the log change.** For positive values the percentage change is
`exp` of the log change minus one. -/
theorem assetReturn_eq_exp_priceLogReturn_sub_one {x₀ x₁ : ℝ} (h₀ : 0 < x₀) (h₁ : 0 < x₁) :
    assetReturn x₀ x₁ = Real.exp (priceLogReturn x₀ x₁) - 1 := by
  have h₀' : x₀ ≠ 0 := ne_of_gt h₀
  have hlog : priceLogReturn x₀ x₁ = Real.log (x₁ / x₀) := by
    simp only [priceLogReturn, logReturn, grossReturn]
  rw [hlog, Real.exp_log (div_pos h₁ h₀)]
  simp only [assetReturn]
  field_simp

/-- **The log change never exceeds the percentage change.** For positive values,
`log (x₁ / x₀) ≤ (x₁ - x₀) / x₀`. For a decline the log change is therefore the larger of the two
in absolute value. -/
theorem priceLogReturn_le_assetReturn {x₀ x₁ : ℝ} (h₀ : 0 < x₀) (h₁ : 0 < x₁) :
    priceLogReturn x₀ x₁ ≤ assetReturn x₀ x₁ := by
  have h₀' : x₀ ≠ 0 := ne_of_gt h₀
  have hlog : priceLogReturn x₀ x₁ = Real.log (x₁ / x₀) := by
    simp only [priceLogReturn, logReturn, grossReturn]
  have heq : (x₁ / x₀ - 1 : ℝ) = assetReturn x₀ x₁ := by
    simp only [assetReturn]
    field_simp
  rw [hlog]
  calc Real.log (x₁ / x₀) ≤ x₁ / x₀ - 1 := Real.log_le_sub_one_of_pos (div_pos h₁ h₀)
    _ = assetReturn x₀ x₁ := heq

/-- **The approximation is exact only without change.** For positive values with `x₁ ≠ x₀`, the
log change is strictly smaller than the percentage change. -/
theorem priceLogReturn_lt_assetReturn {x₀ x₁ : ℝ} (h₀ : 0 < x₀) (h₁ : 0 < x₁) (h : x₁ ≠ x₀) :
    priceLogReturn x₀ x₁ < assetReturn x₀ x₁ := by
  have h₀' : x₀ ≠ 0 := ne_of_gt h₀
  have hlog : priceLogReturn x₀ x₁ = Real.log (x₁ / x₀) := by
    simp only [priceLogReturn, logReturn, grossReturn]
  have heq : (x₁ / x₀ - 1 : ℝ) = assetReturn x₀ x₁ := by
    simp only [assetReturn]
    field_simp
  have hne : x₁ / x₀ ≠ 1 := by
    intro hcon
    rw [div_eq_iff h₀'] at hcon
    exact h (by linarith)
  rw [hlog]
  calc Real.log (x₁ / x₀) < x₁ / x₀ - 1 :=
        Real.log_lt_sub_one_of_pos (div_pos h₁ h₀) hne
    _ = assetReturn x₀ x₁ := heq

/-- **First-order approximation error.** If the percentage change `g` satisfies `|g| ≤ 1 / 2`,
the log change differs from `g` by at most `g ^ 2`. For a positive base this range keeps the
later value in `[x₀ / 2, 3 * x₀ / 2]`, so both values are positive; at a zero base both measures
are the junk value `0`. The bound is an inequality on that range only. -/
theorem abs_priceLogReturn_sub_assetReturn_le {x₀ x₁ : ℝ} (h : |assetReturn x₀ x₁| ≤ 1 / 2) :
    |priceLogReturn x₀ x₁ - assetReturn x₀ x₁| ≤ assetReturn x₀ x₁ ^ 2 := by
  have heq := priceLogReturn_eq_log_one_add_assetReturn x₀ x₁
  rw [heq]
  exact ScalarCalculus.abs_log_one_add_sub_linear_le h

/-- **Common change of units.** Multiplying the base and the later value by the same nonzero
factor (a change of units applied to both) leaves the percentage change unchanged. -/
theorem assetReturn_mul_mul {c : ℝ} (x₀ x₁ : ℝ) (hc : c ≠ 0) :
    assetReturn (c * x₀) (c * x₁) = assetReturn x₀ x₁ := by
  simp only [assetReturn]
  by_cases hx : x₀ = 0
  · simp [hx]
  · have hcx : c * x₀ ≠ 0 := mul_ne_zero hc hx
    field_simp

end MathlibExt.Economics.Finance.PercentAndLogChange
