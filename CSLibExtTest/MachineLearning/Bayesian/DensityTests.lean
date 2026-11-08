/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.Density
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Tests for Bayes' rule for densities
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.Bayesian

namespace CSLibExtTest.MachineLearning.Bayesian.Density

/-- Data whose law does not depend on the parameter leave the prior unchanged: with a `N(0, 1)`
prior and observations `N(5, 2)` regardless of `θ`, the posterior is the prior. -/
example : ∀ᵐ x ∂(Kernel.const ℝ (gaussianReal 5 2) ∘ₘ gaussianReal 0 1),
    ((Kernel.const ℝ (gaussianReal 5 2))†(gaussianReal 0 1)) x = gaussianReal 0 1 := by
  have hae := posterior_ae_eq_of_mul_eq (κ := Kernel.const ℝ (gaussianReal 5 2))
    (μ := gaussianReal 0 1) (ν := volume) (ρ := volume) (p := gaussianPDF 0 1)
    (q := fun _ ↦ gaussianPDF 5 2) (c := gaussianPDF 5 2) (r := fun _ ↦ gaussianPDF 0 1)
    (gaussianReal_of_var_ne_zero _ one_ne_zero)
    (fun _ ↦ by rw [Kernel.const_apply, gaussianReal_of_var_ne_zero _ two_ne_zero])
    (measurable_gaussianPDF _ _) ((measurable_gaussianPDF _ _).comp measurable_snd)
    (measurable_gaussianPDF _ _) ((measurable_gaussianPDF _ _).comp measurable_snd)
    (fun _ ↦ lintegral_gaussianPDF_eq_one _ one_ne_zero) (fun _ _ ↦ mul_comm _ _)
  filter_upwards [hae] with x hx
  rw [hx, gaussianReal_of_var_ne_zero _ one_ne_zero]

end CSLibExtTest.MachineLearning.Bayesian.Density
