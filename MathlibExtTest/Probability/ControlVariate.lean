/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ControlVariate
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.UniformOn

/-!
# Tests for the optimal control-variate coefficient

On three equally likely outcomes, the control takes values `0, 1, 2` and the target takes
values `4, 1, 1`. The optimal coefficient is negative and leaves a nonzero residual variance.
-/

open MeasureTheory ProbabilityTheory MathlibExt.Probability.ControlVariate

namespace MathlibExtTest.Probability.ControlVariate

private noncomputable abbrev μ : Measure (Fin 3) := uniformOn Set.univ
private def h (i : Fin 3) : ℝ := i.val
private def f (i : Fin 3) : ℝ := if i = 0 then 4 else 1

private theorem integral_three (g : Fin 3 → ℝ) : μ[g] = (g 0 + g 1 + g 2) / 3 := by
  rw [integral_fintype (.of_finite (f := g))]
  simp [μ, measureReal_def, uniformOn_univ, Fin.sum_univ_succ, smul_eq_mul]
  ring

private theorem square_integrable (g : Fin 3 → ℝ) : MemLp g 2 μ :=
  (memLp_two_iff_integrable_sq (Integrable.of_finite (f := g)).aestronglyMeasurable).2
    Integrable.of_finite

private theorem mean_control : μ[h] = 1 := by norm_num [integral_three, h]
private theorem mean_target : μ[f] = 2 := by norm_num [integral_three, f]

private theorem var_control : Var[h; μ] = 2 / 3 := by
  rw [variance_eq_sub (square_integrable h), mean_control, integral_three]
  norm_num [h]

private theorem var_target : Var[f; μ] = 2 := by
  rw [variance_eq_sub (square_integrable f), mean_target, integral_three]
  norm_num [f]

private theorem cov_target_control : cov[f, h; μ] = -1 := by
  rw [covariance_eq_sub (square_integrable f) (square_integrable h), mean_target, mean_control,
    integral_three]
  norm_num [Pi.mul_apply, f, h]

private theorem fixed_mean (β : ℝ) : μ[adjusted f h 1 β] = 2 :=
  (integral_adjusted .of_finite .of_finite mean_control β).trans mean_target

private theorem negative_optimum (β : ℝ) :
    IsMinOn (fun b ↦ Var[adjusted f h 1 b; μ]) Set.univ β ↔ β = -3 / 2 := by
  rw [isMinOn_variance_adjusted_iff (square_integrable f) (square_integrable h)
    (by rw [var_control]; norm_num), cov_target_control, var_control]
  norm_num

private theorem minimum_variance : Var[adjusted f h 1 (-3 / 2); μ] = 1 / 2 := by
  have hopt := variance_adjusted_optimal (square_integrable f) (square_integrable h)
    (by rw [var_control]; norm_num) 1
  norm_num [cov_target_control, var_target, var_control] at hopt ⊢
  exact hopt

-- The target can have variance zero: the unique minimizing coefficient is then zero.
private theorem constant_target (β : ℝ) :
    IsMinOn (fun b ↦ Var[adjusted (fun _ ↦ 7) h 1 b; μ]) Set.univ β ↔ β = 0 := by
  rw [isMinOn_variance_adjusted_iff (memLp_const _) (square_integrable h)
    (by rw [var_control]; norm_num)]
  simp

-- An uncorrelated, nonconstant target also has unique minimizer zero.
private theorem uncorrelated_target (β : ℝ) :
    let g := fun i ↦ (h i - 1) ^ 2
    IsMinOn (fun b ↦ Var[adjusted g h 1 b; μ]) Set.univ β ↔ β = 0 := by
  intro g
  have hc : cov[g, h; μ] = 0 := by
    rw [covariance_eq_sub (square_integrable g) (square_integrable h)]
    norm_num [integral_three, g, h, Pi.mul_apply]
  rw [isMinOn_variance_adjusted_iff (square_integrable g) (square_integrable h)
    (by rw [var_control]; norm_num), hc, zero_div]

-- Reusing the observed control itself as the coefficient gives mean 4/3 instead of 2.
private theorem same_observation_bias :
    μ[fun i ↦ adjusted f h 1 (h i) i] = 4 / 3 ∧ μ[fun i ↦ adjusted f h 1 (h i) i] ≠ μ[f] := by
  have hadj : μ[fun i ↦ adjusted f h 1 (h i) i] = 4 / 3 := by
    rw [integral_adjusted_randomCoeff .of_finite (square_integrable h) (square_integrable h)
      mean_control, covariance_self (square_integrable h).aemeasurable, mean_target, var_control]
    norm_num
  exact ⟨hadj, by rw [hadj, mean_target]; norm_num⟩

-- Under the point mass at 1 the control still varies off support. Every coefficient minimizes.
private theorem null_set_variation (β : ℝ) :
    h 0 ≠ h 1 ∧ adjusted f h 1 β =ᵐ[Measure.dirac 1] f ∧
      IsMinOn (fun b ↦ Var[adjusted f h 1 b; Measure.dirac 1]) Set.univ β := by
  have hθ : (∫ i, h i ∂Measure.dirac 1) = 1 := by simp [h]
  have hdeg := adjusted_of_variance_eq_zero (memLp_dirac (by simp)) (variance_dirac 1) hθ f
  exact ⟨by norm_num [h], (hdeg.2 β).1, (hdeg.2 β).2.2⟩

end MathlibExtTest.Probability.ControlVariate
