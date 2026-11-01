/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Moments of the beta law

Mathlib's beta law `betaMeasure α β` has shape parameters `α, β > 0`: its density is
`x ^ (α - 1) (1 - x) ^ (β - 1) / B(α, β)` on `(0, 1)`, where `B(α, β) = Γ(α) Γ(β) / Γ(α + β)`
is `ProbabilityTheory.beta α β`. This file computes its mixed polynomial moments from the
beta-function identity `x ^ k (1 - x) ^ m · Beta(α, β) density = B(α + k, β + m) / B(α, β) ·
Beta(α + k, β + m) density`.

## Main results

* `ProbabilityTheory.integral_betaMeasure`: an integral against `betaMeasure α β` is the
  Lebesgue integral against the density `betaPDFReal α β`; `integral_betaPDFReal`: the density
  integrates to `1`.
* `ProbabilityTheory.beta_add_one_left` (`B(α + 1, β) = B(α, β) α / (α + β)`), `beta_comm`, and
  `betaPDFReal_mul_pow`, the density identity behind the moments.
* `ProbabilityTheory.integral_pow_mul_one_sub_pow_betaMeasure`:
  `E[X ^ k (1 - X) ^ m] = B(α + k, β + m) / B(α, β)`.
* `ProbabilityTheory.integral_id_betaMeasure` (mean `α / (α + β)`),
  `integral_sq_betaMeasure` (`E[X ^ 2] = α (α + 1) / ((α + β) (α + β + 1))`) and
  `integral_mul_one_sub_betaMeasure` (`E[X (1 - X)] = α β / ((α + β) (α + β + 1))`).

All statements assume `α, β > 0`. Outside that range `betaMeasure α β` is not a probability
measure and `beta α β` may vanish, so the identities are not claimed there.

## Provenance

The proof of `betaPDFReal_mul_pow` and the adjacent recurrence are closely adapted from the
existing formalization in `CSLibExt/MachineLearning/Bayesian/BetaBinomial.lean` (same
`betaPDFReal_mul_pow` statement and density computation, there in the beta-binomial /
conjugacy development).

## References

* N. L. Johnson, S. Kotz and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), ch. 25, §2 (moments of the beta distribution).
-/

@[expose] public section

open MeasureTheory Real

namespace ProbabilityTheory

/-- The beta density is nonnegative for positive shape parameters. -/
theorem betaPDFReal_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 hα hβ).le
  · simp [betaPDFReal, hx]

/-- The beta density integrates to `1` (the Bochner-integral form of
`lintegral_betaPDF_eq_one`). -/
theorem integral_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, betaPDFReal α β x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (betaPDFReal_nonneg hα hβ))
    (measurable_betaPDFReal α β).aestronglyMeasurable]
  have h := lintegral_betaPDF_eq_one hα hβ
  simp only [betaPDF] at h
  rw [h, ENNReal.toReal_one]

/-- An integral against `betaMeasure α β` is the integral of the function times the beta
density. No integrability hypothesis is needed: both sides are the junk value `0` together. -/
theorem integral_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (g : ℝ → ℝ) :
    ∫ x, g x ∂betaMeasure α β = ∫ x, betaPDFReal α β x * g x := by
  rw [betaMeasure, show betaPDF α β = fun x => ENNReal.ofReal (betaPDFReal α β x) from rfl,
    integral_withDensity_eq_integral_toReal_smul (measurable_betaPDFReal α β).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (betaPDFReal_nonneg hα hβ _), smul_eq_mul]

/-- `B(α + 1, β) = B(α, β) · α / (α + β)`. -/
theorem beta_add_one_left {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    beta (α + 1) β = beta α β * (α / (α + β)) := by
  have hαβ : 0 < α + β := add_pos hα hβ
  simp only [beta]
  rw [Real.Gamma_add_one hα.ne', show α + 1 + β = (α + β) + 1 by ring,
    Real.Gamma_add_one hαβ.ne']
  have := Real.Gamma_pos_of_pos hαβ
  field_simp

/-- The beta function is symmetric. -/
theorem beta_comm (α β : ℝ) : beta α β = beta β α := by
  simp only [beta, mul_comm, add_comm]

/-- **Beta-function identity for densities**: multiplying the `Beta(α, β)` density by
`x ^ k (1 - x) ^ m` gives `B(α + k, β + m) / B(α, β)` times the `Beta(α + k, β + m)` density. -/
theorem betaPDFReal_mul_pow {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k m : ℕ) (x : ℝ) :
    betaPDFReal α β x * (x ^ k * (1 - x) ^ m) =
      beta (α + k) (β + m) / beta α β * betaPDFReal (α + k) (β + m) x := by
  have hB := (beta_pos hα hβ).ne'
  have hB' := (beta_pos (α := α + k) (β := β + m) (by positivity) (by positivity)).ne'
  unfold betaPDFReal
  split_ifs with h
  · have h1 : 0 < 1 - x := sub_pos.mpr h.2
    rw [show α + k - 1 = (α - 1) + (k : ℝ) by ring, show β + m - 1 = (β - 1) + (m : ℝ) by ring,
      Real.rpow_add h.1, Real.rpow_add h1, Real.rpow_natCast, Real.rpow_natCast]
    field_simp
  · simp

/-- **Mixed moments of the beta law**: for `α, β > 0` and natural `k, m`,
`E[X ^ k (1 - X) ^ m] = B(α + k, β + m) / B(α, β)`. -/
theorem integral_pow_mul_one_sub_pow_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (k m : ℕ) :
    ∫ x, x ^ k * (1 - x) ^ m ∂betaMeasure α β = beta (α + k) (β + m) / beta α β := by
  rw [integral_betaMeasure hα hβ]
  simp_rw [betaPDFReal_mul_pow hα hβ k m]
  rw [integral_const_mul, integral_betaPDFReal (by positivity) (by positivity), mul_one]

/-- **Mean of the beta law**: for `α, β > 0`, `E[X] = α / (α + β)`. -/
theorem integral_id_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, x ∂betaMeasure α β = α / (α + β) := by
  have h := integral_pow_mul_one_sub_pow_betaMeasure hα hβ 1 0
  simp only [pow_one, pow_zero, mul_one, Nat.cast_one, Nat.cast_zero, add_zero] at h
  rw [h, beta_add_one_left hα hβ, mul_div_cancel_left₀ _ (beta_pos hα hβ).ne']

/-- **Second moment of the beta law**: for `α, β > 0`,
`E[X ^ 2] = α (α + 1) / ((α + β) (α + β + 1))`. -/
theorem integral_sq_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, x ^ 2 ∂betaMeasure α β = α * (α + 1) / ((α + β) * (α + β + 1)) := by
  have h := integral_pow_mul_one_sub_pow_betaMeasure hα hβ 2 0
  simp only [pow_zero, mul_one, Nat.cast_ofNat, Nat.cast_zero, add_zero] at h
  rw [h, show α + 2 = (α + 1) + 1 by ring, beta_add_one_left (by positivity) hβ,
    beta_add_one_left hα hβ]
  have := (beta_pos hα hβ).ne'
  have : α + β ≠ 0 := by positivity
  have : α + 1 + β ≠ 0 := by positivity
  field_simp
  ring

/-- For `α, β > 0`, `E[X (1 - X)] = α β / ((α + β) (α + β + 1))` (half the expected
heterozygosity of a `Beta(α, β)` allele frequency). -/
theorem integral_mul_one_sub_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, x * (1 - x) ∂betaMeasure α β = α * β / ((α + β) * (α + β + 1)) := by
  have h := integral_pow_mul_one_sub_pow_betaMeasure hα hβ 1 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h, beta_add_one_left hα (by positivity), beta_comm α (β + 1),
    beta_add_one_left hβ hα, beta_comm β α]
  have := (beta_pos hα hβ).ne'
  have : α + β ≠ 0 := by positivity
  have : β + α ≠ 0 := by positivity
  have : α + (β + 1) ≠ 0 := by positivity
  field_simp
  ring

end ProbabilityTheory
