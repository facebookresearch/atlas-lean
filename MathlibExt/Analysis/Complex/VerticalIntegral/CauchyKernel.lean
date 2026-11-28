/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Cauchy kernel on a vertical line

Closed forms for `∫ σ / (σ² + t²) dt` and `∫ dt / (σ + it)` and the pointwise facts behind
them. These are the basic integrals met on a vertical line `re s = σ`. Mathlib has
`integral_div_sq_add_sq` over an arbitrary interval; the symmetric closed form
`∫_{-T}^{T} dt / (σ + it) = 2 arctan (T / σ)` is `Complex.vertical_side_one_div` in
`MathlibExt.Analysis.Complex.RectilinearCycle`.

## Main statements

* `Complex.ofReal_add_mul_I_ne_zero`, `Complex.one_div_ofReal_add_mul_I`: nonvanishing and
  the real/imaginary split of `1 / (σ + it)`.
* `Real.hasDerivAt_arctan_div`, `Real.hasDerivAt_half_log_sq_add_sq`: the antiderivatives.
* `integral_div_sq_add_sq_neg_self`: `∫_{-R}^{R} σ / (σ² + t²) dt = 2 arctan (R / σ)`.
* `Complex.integral_one_div_ofReal_add_mul_I`: `∫_a^b dt / (σ + it)` in closed form.
-/

@[expose] public section

/-- `σ + it ≠ 0` as soon as one coordinate is nonzero. -/
theorem Complex.ofReal_add_mul_I_ne_zero {σ t : ℝ} (h : σ ≠ 0 ∨ t ≠ 0) :
    (σ : ℂ) + t * Complex.I ≠ 0 := by
  intro hz
  have h1 : σ = 0 := by simpa using congrArg Complex.re hz
  have h2 : t = 0 := by simpa using congrArg Complex.im hz
  rcases h with h | h
  · exact h h1
  · exact h h2

/-- The real/imaginary split `1 / (σ + it) = σ / (σ² + t²) - i t / (σ² + t²)`. -/
theorem Complex.one_div_ofReal_add_mul_I {σ t : ℝ} (h : σ ^ 2 + t ^ 2 ≠ 0) :
    (1 : ℂ) / (σ + t * Complex.I) =
      ((σ / (σ ^ 2 + t ^ 2) : ℝ) : ℂ) - Complex.I * ((t / (σ ^ 2 + t ^ 2) : ℝ) : ℂ) := by
  have hcc : (σ : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h
  have hne : (σ : ℂ) + t * Complex.I ≠ 0 := by
    refine Complex.ofReal_add_mul_I_ne_zero ?_
    by_contra! h0
    exact h (by rw [h0.1, h0.2]; ring)
  push_cast
  rw [div_eq_iff hne]
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- `u ↦ arctan (u / σ)` has derivative `σ / (σ² + t²)`. -/
theorem Real.hasDerivAt_arctan_div {σ : ℝ} (hσ : σ ≠ 0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.arctan (u / σ)) (σ / (σ ^ 2 + t ^ 2)) t := by
  have h1 : HasDerivAt (fun u : ℝ => u / σ) (1 / σ) t := by
    simpa using (hasDerivAt_id t).div_const σ
  have key : σ / (σ ^ 2 + t ^ 2) = 1 / (1 + (t / σ) ^ 2) * (1 / σ) := by field_simp
  rw [key]
  exact (Real.hasDerivAt_arctan (t / σ)).comp t h1

/-- `u ↦ (1 / 2) log (σ² + u²)` has derivative `t / (σ² + t²)`. -/
theorem Real.hasDerivAt_half_log_sq_add_sq {σ t : ℝ} (h : σ ^ 2 + t ^ 2 ≠ 0) :
    HasDerivAt (fun u : ℝ => 1 / 2 * Real.log (σ ^ 2 + u ^ 2)) (t / (σ ^ 2 + t ^ 2)) t := by
  have h1 : HasDerivAt (fun u : ℝ => σ ^ 2 + u ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add (σ ^ 2)
  have key : t / (σ ^ 2 + t ^ 2) = 1 / 2 * ((σ ^ 2 + t ^ 2)⁻¹ * (2 * t)) := by ring
  rw [key]
  exact ((Real.hasDerivAt_log h).comp t h1).const_mul (1 / 2 : ℝ)

/-- The Cauchy kernel `t ↦ σ / (σ² + t²)` is continuous for `σ ≠ 0`. -/
theorem Real.continuous_div_sq_add_sq {σ : ℝ} (hσ : σ ≠ 0) :
    Continuous fun t : ℝ => σ / (σ ^ 2 + t ^ 2) :=
  continuous_const.div (by fun_prop) fun t => by positivity

/-- **The symmetric Cauchy kernel.** `∫_{-R}^{R} σ / (σ² + t²) dt = 2 arctan (R / σ)`. -/
theorem integral_div_sq_add_sq_neg_self (σ R : ℝ) :
    ∫ t in (-R)..R, σ / (σ ^ 2 + t ^ 2) = 2 * Real.arctan (R / σ) := by
  rw [integral_div_sq_add_sq, neg_div, Real.arctan_neg]
  ring

/-- **The complex Cauchy kernel on a vertical line.** For `σ ≠ 0`,
`∫_a^b dt / (σ + it) = (arctan (b / σ) - arctan (a / σ)) -
i ((1/2) log (σ² + b²) - (1/2) log (σ² + a²))`. -/
theorem Complex.integral_one_div_ofReal_add_mul_I {σ : ℝ} (hσ : σ ≠ 0) (a b : ℝ) :
    ∫ t in a..b, (1 : ℂ) / (σ + t * Complex.I) =
      ((Real.arctan (b / σ) - Real.arctan (a / σ) : ℝ) : ℂ) -
        Complex.I * ((1 / 2 * Real.log (σ ^ 2 + b ^ 2) -
          1 / 2 * Real.log (σ ^ 2 + a ^ 2) : ℝ) : ℂ) := by
  have hF : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => ((Real.arctan (u / σ) : ℝ) : ℂ) -
          Complex.I * (((1 / 2) * Real.log (σ ^ 2 + u ^ 2) : ℝ) : ℂ))
        ((1 : ℂ) / (σ + t * Complex.I)) t := by
    intro t _
    have hs : σ ^ 2 + t ^ 2 ≠ 0 := by positivity
    rw [Complex.one_div_ofReal_add_mul_I hs]
    exact (Real.hasDerivAt_arctan_div hσ t).ofReal_comp.sub
      ((Real.hasDerivAt_half_log_sq_add_sq hs).ofReal_comp.const_mul Complex.I)
  have hcont : Continuous fun t : ℝ => (1 : ℂ) / (σ + t * Complex.I) :=
    continuous_const.div (by fun_prop) fun t => Complex.ofReal_add_mul_I_ne_zero (Or.inl hσ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable _ _)]
  push_cast
  ring
