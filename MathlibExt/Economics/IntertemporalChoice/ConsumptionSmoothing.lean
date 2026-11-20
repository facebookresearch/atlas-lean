/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.IntertemporalChoice.EulerEquation
public import Mathlib.Order.Monotone.Basic

/-!
# Consumption smoothing when `β (1 + r) = 1`

With `β (1 + r) = 1` the two-period Euler equation `u'(c₀) = β (1 + r) u'(c₁)` (MA04.T02,
`euler_equation`) reads `u'(c₀) = u'(c₁)`. If marginal utility is strictly decreasing on
positive consumption it is injective there, so interior optimal consumption is equal
across the two dates.

## Main results

* `MathlibExt.Economics.IntertemporalChoice.eq_of_euler_of_discount_mul_gross_eq_one`:
  the Euler equation with `β (1 + r) = 1` forces `c₀ = c₁` (`StrictAntiOn.injOn`).
* `MathlibExt.Economics.IntertemporalChoice.consumption_eq_of_discount_mul_gross_eq_one`:
  an interior maximizer of lifetime utility consumes the same amount in both periods.

No concavity, `0 < β` or `0 < 1 + r` is assumed; strict decrease is only required on
`(0, ∞)`, which covers log utility.

## References

MIT 14.05 Intermediate Macroeconomics (consumption smoothing). Atlas roadmap target
MA04.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.IntertemporalChoice

/-- Consumption equalization from the Euler equation: if `u'(c₀) = β (1 + r) u'(c₁)`
with `β (1 + r) = 1` and marginal utility `u'` strictly decreasing on positive
consumption, then `c₀ = c₁` for positive `c₀, c₁`. -/
theorem eq_of_euler_of_discount_mul_gross_eq_one {u : ℝ → ℝ} {β r c₀ c₁ : ℝ}
    (heuler : deriv u c₀ = β * (1 + r) * deriv u c₁) (hβr : β * (1 + r) = 1)
    (hmu : StrictAntiOn (deriv u) (Set.Ioi 0)) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    c₀ = c₁ := by
  rw [hβr, one_mul] at heuler
  exact hmu.injOn hc₀ hc₁ heuler

/-- Consumption smoothing: with `β (1 + r) = 1` and strictly decreasing marginal
utility, an unconstrained interior maximizer of two-period lifetime utility
consumes the same amount in both periods (Atlas roadmap MA04.T03). -/
theorem consumption_eq_of_discount_mul_gross_eq_one {u : ℝ → ℝ} {β r y₀ y₁ c₀ : ℝ}
    (hmax : IsMaxOn (lifetimeUtility u β r y₀ y₁) (feasibleConsumption r y₀ y₁) c₀)
    (hc₀ : 0 < c₀) (hc₁ : 0 < secondPeriodConsumption r y₀ y₁ c₀)
    (hu₀ : DifferentiableAt ℝ u c₀)
    (hu₁ : DifferentiableAt ℝ u (secondPeriodConsumption r y₀ y₁ c₀))
    (hβr : β * (1 + r) = 1) (hmu : StrictAntiOn (deriv u) (Set.Ioi 0)) :
    c₀ = secondPeriodConsumption r y₀ y₁ c₀ := by
  have heuler := euler_equation hmax hc₀ hc₁ hu₀ hu₁
  exact eq_of_euler_of_discount_mul_gross_eq_one heuler hβr hmu hc₀ hc₁

end MathlibExt.Economics.IntertemporalChoice
