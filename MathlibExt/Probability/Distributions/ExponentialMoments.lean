/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Variance

/-!
# Moments of the exponential distribution

Mathlib defines the exponential law of rate `r` as `expMeasure r := gammaMeasure 1 r`, with
density `r * exp (-(r * x))` on `[0, ∞)`. This file computes its moments: the `n`-th moment is
`n! / r ^ n`; in particular the mean is `r⁻¹`, the second moment is `2 / r ^ 2` and the variance
is `r⁻¹ ^ 2`. The results are transported to random variables via `HasLaw`.

## Main results

* `ProbabilityTheory.integral_expMeasure_eq_setIntegral`: integrals against `expMeasure r` as
  integrals of `r * exp (-(r * x)) * f x` over `Ioi 0`.
* `ProbabilityTheory.integrable_pow_expMeasure`, `ProbabilityTheory.integral_pow_expMeasure`:
  `∫ x, x ^ n ∂(expMeasure r) = n ! / r ^ n`.
* `ProbabilityTheory.integrable_id_expMeasure`, `ProbabilityTheory.integral_id_expMeasure`:
  the mean is `r⁻¹`.
* `ProbabilityTheory.integral_sq_expMeasure`: the second moment is `2 / r ^ 2`.
* `ProbabilityTheory.variance_id_expMeasure`: the variance is `r⁻¹ ^ 2`.
* `ProbabilityTheory.HasLaw.integral_eq_inv_of_expMeasure`,
  `ProbabilityTheory.HasLaw.variance_eq_of_expMeasure`: the same for a random variable with
  law `expMeasure r`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.
  (1971), §I.3.
-/

open MeasureTheory Set Real

open scoped Nat

namespace ProbabilityTheory

@[expose] public section

noncomputable section

/-- The rate-`r` exponential density times `f`, as an indicator on `Ici 0`. -/
lemma gammaPDFReal_one_eq_indicator {r : ℝ} (f : ℝ → ℝ) :
    (fun x => gammaPDFReal 1 r x * f x)
      = (Ici (0 : ℝ)).indicator (fun x => r * exp (-(r * x)) * f x) := by
  funext x
  by_cases hx : 0 ≤ x
  · simp [gammaPDFReal, hx]
  · simp [gammaPDFReal, hx]

/-- Integrals against the exponential law of rate `r > 0` are integrals of
`r * exp (-(r * x)) * f x` over `(0, ∞)`. -/
theorem integral_expMeasure_eq_setIntegral {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x ∂(expMeasure r) = ∫ x in Ioi 0, r * exp (-(r * x)) * f x := by
  rw [expMeasure, integral_gammaMeasure_eq_integral_smul]
  simp_rw [toReal_gammaPDF one_pos hr, smul_eq_mul]
  rw [gammaPDFReal_one_eq_indicator, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi]

/-- A function is integrable against the exponential law of rate `r > 0` iff
`r * exp (-(r * x)) * f x` is integrable on `(0, ∞)`. -/
theorem integrable_expMeasure_iff {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ} :
    Integrable f (expMeasure r)
      ↔ IntegrableOn (fun x => r * exp (-(r * x)) * f x) (Ioi 0) := by
  rw [expMeasure, integrable_gammaMeasure_iff]
  simp_rw [toReal_gammaPDF one_pos hr, smul_eq_mul]
  rw [gammaPDFReal_one_eq_indicator, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]

/-- Rewriting `x ^ n` times the exponential density in the gamma-integrand form. -/
lemma pow_eq_rpow_mul_exp (r x : ℝ) (n : ℕ) :
    r * exp (-(r * x)) * x ^ n = r * (x ^ (((n + 1 : ℕ) : ℝ) - 1) * exp (-(r * x))) := by
  rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, rpow_natCast]
  ring

/-- All moments of the exponential law are finite. -/
theorem integrable_pow_expMeasure {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Integrable (fun x => x ^ n) (expMeasure r) := by
  rw [integrable_expMeasure_iff hr]
  have h : IntegrableOn (fun x => r * (x ^ (((n + 1 : ℕ) : ℝ) - 1) * exp (-(r * x))))
      (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi (a := ((n + 1 : ℕ) : ℝ)) (by positivity) hr).const_mul r
  exact h.congr_fun (fun x _ => (pow_eq_rpow_mul_exp r x n).symm) measurableSet_Ioi

/-- The `n`-th moment of the exponential law of rate `r > 0` is `n! / r ^ n`. -/
theorem integral_pow_expMeasure {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∫ x, x ^ n ∂(expMeasure r) = n ! / r ^ n := by
  rw [integral_expMeasure_eq_setIntegral hr,
    setIntegral_congr_fun measurableSet_Ioi (fun x _ => pow_eq_rpow_mul_exp r x n),
    integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr]
  rw [Nat.cast_add, Nat.cast_one, Gamma_nat_eq_factorial, ← Nat.cast_succ, rpow_natCast]
  rw [one_div, inv_pow, pow_succ]
  field_simp

/-- The identity is integrable against the exponential law. -/
theorem integrable_id_expMeasure {r : ℝ} (hr : 0 < r) : Integrable id (expMeasure r) := by
  simpa [Function.id_def] using integrable_pow_expMeasure hr 1

/-- The mean of the exponential law of rate `r > 0` is `r⁻¹`. -/
theorem integral_id_expMeasure {r : ℝ} (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = r⁻¹ := by
  simpa using integral_pow_expMeasure hr 1

/-- The second moment of the exponential law of rate `r > 0` is `2 / r ^ 2`. -/
theorem integral_sq_expMeasure {r : ℝ} (hr : 0 < r) :
    ∫ x, x ^ 2 ∂(expMeasure r) = 2 / r ^ 2 := by
  simpa using integral_pow_expMeasure hr 2

/-- The variance of the exponential law of rate `r > 0` is `r⁻¹ ^ 2`. -/
theorem variance_id_expMeasure {r : ℝ} (hr : 0 < r) : Var[id; expMeasure r] = r⁻¹ ^ 2 := by
  have := isProbabilityMeasure_expMeasure hr
  have hm : MemLp id 2 (expMeasure r) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using integrable_pow_expMeasure hr 2)
  rw [variance_eq_sub hm]
  simp only [id_eq, Pi.pow_apply]
  rw [integral_sq_expMeasure hr, integral_id_expMeasure hr]
  field_simp
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {r : ℝ}

/-- A random variable with exponential law of rate `r > 0` is integrable. -/
theorem HasLaw.integrable_of_expMeasure (hX : HasLaw X (expMeasure r) μ) (hr : 0 < r) :
    Integrable X μ :=
  hX.integrable (integrable_id_expMeasure hr)

/-- A random variable with exponential law of rate `r > 0` has mean `r⁻¹`. -/
theorem HasLaw.integral_eq_inv_of_expMeasure (hX : HasLaw X (expMeasure r) μ) (hr : 0 < r) :
    μ[X] = r⁻¹ := by
  rw [hX.integral_eq, integral_id_expMeasure hr]

/-- A random variable with exponential law of rate `r > 0` has variance `r⁻¹ ^ 2`. -/
theorem HasLaw.variance_eq_of_expMeasure (hX : HasLaw X (expMeasure r) μ) (hr : 0 < r) :
    Var[X; μ] = r⁻¹ ^ 2 := by
  rw [hX.variance_eq, variance_id_expMeasure hr]

end

end

end ProbabilityTheory
