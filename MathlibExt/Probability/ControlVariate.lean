/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Order.Filter.Extr

/-!
# The optimal control-variate coefficient

Subtracting a fixed multiple of a centered control preserves the target's mean. Completing the
square in the adjusted variance identifies the minimizing coefficient and the exact cost of
using any other coefficient. A control of zero variance changes nothing almost surely.

Art B. Owen, *Monte Carlo Theory, Methods and Examples*, chapter 8, §8.9, p. 29:
equation (8.29) defines the estimator; the following displays give its variance, optimal
coefficient and correlation form of the minimum. We consider one observation (`n = 1`).
The zero-variance case follows from almost-sure constancy and needs no division. For a random
coefficient we also compute the exact bias as a covariance; compare Owen's discussion of fitting
a coefficient on the same sample on p. 30 and the error decomposition (8.34) on pp. 31–32.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.ControlVariate

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {f h : Ω → ℝ} {θ : ℝ}

/-- Adjust the target `f` by subtracting `β` times the deviation of the control `h` from `θ`. -/
def adjusted (f h : Ω → ℝ) (θ β : ℝ) (ω : Ω) : ℝ := f ω - β * (h ω - θ)

/-- When `θ` is the known control mean, every fixed coefficient preserves the target mean. -/
theorem integral_adjusted (hf : Integrable f μ) (hh : Integrable h μ) (hθ : μ[h] = θ) (β : ℝ) :
    μ[adjusted f h θ β] = μ[f] := by
  have hc : Integrable (fun ω ↦ h ω - θ) μ := hh.sub (integrable_const θ)
  unfold adjusted
  rw [integral_sub hf (hc.const_mul β), integral_const_mul,
    integral_sub hh (integrable_const θ), integral_const]
  simp [hθ]

/-- On a probability space with law `μ`, let `f` be an integrable real target and let the random
coefficient `b` and control `h` be square-integrable and real-valued. If `θ = μ[h]`, then the
adjusted variable `ω ↦ f ω - b ω * (h ω - θ)` has expectation `μ[f] - cov[b, h; μ]`. -/
theorem integral_adjusted_randomCoeff (hf : Integrable f μ) (hh : MemLp h 2 μ)
    {b : Ω → ℝ} (hb : MemLp b 2 μ) (hθ : μ[h] = θ) :
    μ[fun ω ↦ adjusted f h θ (b ω) ω] = μ[f] - cov[b, h; μ] := by
  have hc : MemLp (fun ω ↦ h ω - θ) 2 μ := hh.sub (memLp_const θ)
  have hz : μ[fun ω ↦ h ω - θ] = 0 := by
    rw [integral_sub (hh.integrable one_le_two) (integrable_const θ), integral_const]
    simp [hθ]
  have hcov := covariance_eq_sub hb hc
  rw [covariance_sub_const_right (hh.integrable one_le_two), hz, mul_zero, sub_zero] at hcov
  exact (integral_sub hf (hb.integrable_mul hc)).trans (congrArg (μ[f] - ·) hcov.symm)

/-- The adjusted variance is a quadratic in the coefficient. It does not depend on the
centering constant, since that constant only shifts the adjusted variable. -/
theorem variance_adjusted (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) (θ β : ℝ) :
    Var[adjusted f h θ β; μ] = Var[f; μ] - 2 * β * cov[f, h; μ] + β ^ 2 * Var[h; μ] := by
  have hc : MemLp (fun ω ↦ h ω - θ) 2 μ := hh.sub (memLp_const θ)
  unfold adjusted
  rw [variance_fun_sub hf (hc.const_mul β), covariance_const_mul_right,
    covariance_sub_const_right (hh.integrable one_le_two), variance_const_mul,
    variance_sub_const hh.aestronglyMeasurable]
  ring

/-- Completing the square: the excess over the minimum is the control variance times the
squared distance from the optimal coefficient. -/
theorem variance_adjusted_eq_min_add_sq (hf : MemLp f 2 μ) (hh : MemLp h 2 μ)
    (hv : 0 < Var[h; μ]) (θ β : ℝ) :
    Var[adjusted f h θ β; μ] = Var[f; μ] - cov[f, h; μ] ^ 2 / Var[h; μ] +
      Var[h; μ] * (β - cov[f, h; μ] / Var[h; μ]) ^ 2 := by
  rw [variance_adjusted hf hh]
  field_simp [hv.ne']
  ring

/-- The variance attained at the covariance-to-control-variance ratio. Only the control
variance must be positive; the target can be constant. -/
theorem variance_adjusted_optimal (hf : MemLp f 2 μ) (hh : MemLp h 2 μ)
    (hv : 0 < Var[h; μ]) (θ : ℝ) :
    Var[adjusted f h θ (cov[f, h; μ] / Var[h; μ]); μ] =
      Var[f; μ] - cov[f, h; μ] ^ 2 / Var[h; μ] := by
  simp [variance_adjusted_eq_min_add_sq hf hh hv]

/-- A coefficient minimizes the variance over all real coefficients if and only if it is the
covariance-to-control-variance ratio, provided the control variance is positive. -/
theorem isMinOn_variance_adjusted_iff (hf : MemLp f 2 μ) (hh : MemLp h 2 μ)
    (hv : 0 < Var[h; μ]) (θ β : ℝ) :
    IsMinOn (fun b ↦ Var[adjusted f h θ b; μ]) Set.univ β ↔ β = cov[f, h; μ] / Var[h; μ] := by
  rw [isMinOn_univ_iff]
  constructor
  · intro hmin
    have hle := hmin (cov[f, h; μ] / Var[h; μ])
    rw [variance_adjusted_optimal hf hh hv, variance_adjusted_eq_min_add_sq hf hh hv] at hle
    by_contra hne
    linarith [mul_pos hv (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))]
  · rintro rfl b
    rw [variance_adjusted_optimal hf hh hv, variance_adjusted_eq_min_add_sq hf hh hv]
    exact le_add_of_nonneg_right (mul_nonneg hv.le (sq_nonneg _))

/-- For positive target and control variances, the minimum is `(1 - ρ²) Var[f]`, where `ρ`
is the population covariance divided by the product of the two standard deviations. -/
theorem variance_adjusted_optimal_eq_one_sub_corr_sq (hf : MemLp f 2 μ) (hh : MemLp h 2 μ)
    (vf : 0 < Var[f; μ]) (vh : 0 < Var[h; μ]) (θ : ℝ) :
    Var[adjusted f h θ (cov[f, h; μ] / Var[h; μ]); μ] =
      (1 - (cov[f, h; μ] / (√Var[f; μ] * √Var[h; μ])) ^ 2) * Var[f; μ] := by
  rw [variance_adjusted_optimal hf hh vh, div_pow, mul_pow, Real.sq_sqrt vf.le, Real.sq_sqrt vh.le]
  field_simp [vf.ne', vh.ne']

/-- A zero-variance control equals its known mean almost surely. Thus every fixed coefficient
leaves the target unchanged almost surely, preserves its variance, and is a global minimizer. -/
theorem adjusted_of_variance_eq_zero (hh : MemLp h 2 μ) (hv : Var[h; μ] = 0) (hθ : μ[h] = θ)
    (f : Ω → ℝ) :
    (∀ᵐ ω ∂μ, h ω = θ) ∧ ∀ β : ℝ, adjusted f h θ β =ᵐ[μ] f ∧
      Var[adjusted f h θ β; μ] = Var[f; μ] ∧
      IsMinOn (fun b ↦ Var[adjusted f h θ b; μ]) Set.univ β := by
  have hc := hθ ▸ ae_eq_integral_of_variance_eq_zero hh hv
  have heq (β : ℝ) : adjusted f h θ β =ᵐ[μ] f := by
    filter_upwards [hc] with ω hω
    simp [adjusted, hω]
  exact ⟨hc, fun β ↦ ⟨heq β, variance_congr (heq β), isMinOn_univ_iff.mpr fun b ↦
    le_of_eq ((variance_congr (heq β)).trans (variance_congr (heq b)).symm)⟩⟩

end MathlibExt.Probability.ControlVariate
