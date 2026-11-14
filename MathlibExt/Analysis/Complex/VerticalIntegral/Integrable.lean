/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import MathlibExt.Analysis.Complex.VerticalIntegral.CauchyKernel

/-!
# Integrability on a vertical line

For `c > 0`, a continuous function `g` with `‖g t‖ ≤ M / ‖c + it‖ ^ (n + 2)` is integrable on
`ℝ`, with `∫_{-R}^{R} ‖g‖ ≤ π M / c ^ (n + 1)` uniformly in `R`. This is the comparison with the
Cauchy kernel `c / (c² + t²)`, and is the integrability input for every Perron-type kernel of
order at least two.

## Main statements

* `Complex.le_norm_ofReal_add_mul_I`: `σ ≤ ‖σ + it‖` for `σ > 0`.
* `Complex.intervalIntegral_norm_le_of_norm_le_div_pow`: the uniform bound on truncated
  `L¹` norms.
* `Complex.integrable_of_norm_le_div_pow`, `Complex.verticalIntegrable_of_norm_le_div_pow`:
  integrability on the line.
-/

@[expose] public section

open MeasureTheory

namespace Complex

/-- The real part bounds the modulus: `σ ≤ ‖σ + it‖` for `σ > 0`. -/
theorem le_norm_ofReal_add_mul_I {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : σ ≤ ‖(σ : ℂ) + t * I‖ := by
  have h := abs_re_le_norm ((σ : ℂ) + t * I)
  rwa [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero, abs_of_pos hσ] at h

/-- **Truncated `L¹` bound on a vertical line.** If `c > 0` and the continuous `g` satisfies
`‖g t‖ ≤ M / ‖c + it‖ ^ (n + 2)`, then `∫_{-R}^{R} ‖g‖ ≤ M / c ^ (n + 1) * π`. -/
theorem intervalIntegral_norm_le_of_norm_le_div_pow {c : ℝ} (hc : 0 < c) {n : ℕ} {M : ℝ}
    (hM : 0 ≤ M) {g : ℝ → ℂ} (hg : Continuous g)
    (hb : ∀ t : ℝ, ‖g t‖ ≤ M / ‖(c : ℂ) + t * I‖ ^ (n + 2)) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (-R)..R, ‖g t‖ ≤ M / c ^ (n + 1) * Real.pi := by
  have hab : -R ≤ R := by linarith
  have hpt : ∀ t ∈ Set.Icc (-R) R, ‖g t‖ ≤ M / c ^ (n + 1) * (c / (c ^ 2 + t ^ 2)) := by
    intro t _
    refine (hb t).trans ?_
    have hden : c ^ n * (c ^ 2 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ ^ (n + 2) := by
      have h1 : c ^ n ≤ ‖(c : ℂ) + t * I‖ ^ n :=
        pow_le_pow_left₀ hc.le (le_norm_ofReal_add_mul_I hc t) n
      have h2 : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
        rw [Complex.sq_norm, normSq_add_mul_I]
      rw [pow_add, h2]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hpos : 0 < c ^ n * (c ^ 2 + t ^ 2) := by positivity
    refine (div_le_div_of_nonneg_left hM hpos hden).trans_eq ?_
    field_simp
    ring
  calc ∫ t in (-R)..R, ‖g t‖
      ≤ ∫ t in (-R)..R, M / c ^ (n + 1) * (c / (c ^ 2 + t ^ 2)) :=
        intervalIntegral.integral_mono_on hab (hg.norm.intervalIntegrable _ _)
          ((continuous_const.mul (Real.continuous_div_sq_add_sq hc.ne')).intervalIntegrable _ _)
          hpt
    _ = M / c ^ (n + 1) * (2 * Real.arctan (R / c)) := by
        rw [intervalIntegral.integral_const_mul, integral_div_sq_add_sq_neg_self]
    _ ≤ M / c ^ (n + 1) * Real.pi :=
        mul_le_mul_of_nonneg_left (by linarith [Real.arctan_lt_pi_div_two (R / c)])
          (div_nonneg hM (by positivity))

/-- **Integrability on a vertical line.** For `c > 0`, a continuous `g` with
`‖g t‖ ≤ M / ‖c + it‖ ^ (n + 2)` is integrable on `ℝ`. -/
theorem integrable_of_norm_le_div_pow {c : ℝ} (hc : 0 < c) {n : ℕ} {M : ℝ} (hM : 0 ≤ M)
    {g : ℝ → ℂ} (hg : Continuous g) (hb : ∀ t : ℝ, ‖g t‖ ≤ M / ‖(c : ℂ) + t * I‖ ^ (n + 2)) :
    Integrable g := by
  refine integrable_of_intervalIntegral_norm_bounded (M / c ^ (n + 1) * Real.pi)
    (a := fun R : ℝ => -R) (b := fun R : ℝ => R) (fun R => hg.integrableOn_Ioc)
    Filter.tendsto_neg_atTop_atBot Filter.tendsto_id ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
  exact intervalIntegral_norm_le_of_norm_le_div_pow hc hM hg hb hR

/-- **Integrability on a vertical line.** For `c > 0`, if `t ↦ f (c + it)` is continuous and
`‖f (c + it)‖ ≤ M / ‖c + it‖ ^ (n + 2)`, then `f` is vertically integrable at `c`. -/
theorem verticalIntegrable_of_norm_le_div_pow {c : ℝ} (hc : 0 < c) {n : ℕ} {M : ℝ}
    (hM : 0 ≤ M) {f : ℂ → ℂ} (hf : Continuous fun t : ℝ => f (c + t * I))
    (hb : ∀ t : ℝ, ‖f (c + t * I)‖ ≤ M / ‖(c : ℂ) + t * I‖ ^ (n + 2)) :
    VerticalIntegrable f c :=
  integrable_of_norm_le_div_pow hc hM hf hb

end Complex
