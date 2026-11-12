/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.NormalNormal
import Mathlib.Probability.ProductMeasure

@[expose] public section

/-! # Normal-normal posterior for the one-draw Gaussian marginal kernel

The one-draw marginal (product-sample) law coincides with the Gaussian likelihood. This file
packages that law as `marginalGaussianKernel` (a density-defined kernel, agreeing with
`gaussianLikelihood` for `v ≠ 0`), proves the packaging equals the likelihood by kernel
extensionality through the marginal identity, and states the posterior and evidence with the
kernel. -/

namespace Cslib.MachineLearning.Bayesian

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

/-- **One-draw marginal law.** The pushforward of the one-observation iid Gaussian tuple law
along evaluation equals the Gaussian likelihood. -/
theorem gaussianMarginalLaw_one_eq_gaussianLikelihood (θ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    (Measure.pi fun _ : Fin 1 => gaussianReal θ v).map (fun s => s 0) =
      gaussianLikelihood v θ := by
  rw [gaussianLikelihood_apply h]
  exact (measurePreserving_eval (fun _ : Fin 1 => gaussianReal θ v) 0).map_eq

/-- The one-draw Gaussian sampling kernel: the law of a single `N(θ, v)` observation,
packaged with its Gaussian density. It agrees with `gaussianLikelihood` for `v ≠ 0` and
differs at `v = 0` (there is no Dirac branch). -/
noncomputable def marginalGaussianKernel (v : ℝ≥0) : Kernel ℝ ℝ :=
  (Kernel.const ℝ volume).withDensity fun θ x => gaussianPDF θ v x

/-- The marginal kernel's law at `θ` is the one-draw product-sample law. -/
theorem marginalGaussianKernel_apply_pi {v : ℝ≥0} (h : v ≠ 0) (θ : ℝ) :
    marginalGaussianKernel v θ =
      (Measure.pi fun _ : Fin 1 => gaussianReal θ v).map (fun s => s 0) := by
  have hmeas : Measurable (Function.uncurry fun θ x : ℝ => gaussianPDF θ v x) := by
    fun_prop
  unfold marginalGaussianKernel
  rw [Kernel.withDensity_apply _ hmeas, Kernel.const_apply, ← gaussianLikelihood_apply' h θ]
  exact (gaussianMarginalLaw_one_eq_gaussianLikelihood θ h).symm

/-- The marginal sampling kernel coincides with the Gaussian likelihood for nondegenerate
noise, by kernel extensionality through the marginal identity. -/
theorem marginalGaussianKernel_eq_gaussianLikelihood {v : ℝ≥0} (h : v ≠ 0) :
    marginalGaussianKernel v = gaussianLikelihood v := by
  apply Kernel.ext
  intro θ
  rw [marginalGaussianKernel_apply_pi h θ]
  exact gaussianMarginalLaw_one_eq_gaussianLikelihood θ h

instance {v : ℝ≥0} : IsFiniteKernel (marginalGaussianKernel v) := by
  by_cases h : v = 0
  · subst h
    refine ⟨0, by simp, fun θ => ?_⟩
    have h0 : marginalGaussianKernel (0 : ℝ≥0) θ = 0 := by
      unfold marginalGaussianKernel
      rw [Kernel.withDensity_apply _ (measurable_gaussianPDF_mean 0), Kernel.const_apply,
        gaussianPDF_zero_var, MeasureTheory.withDensity_zero]
    rw [h0]
    simp
  · rw [marginalGaussianKernel_eq_gaussianLikelihood h]
    infer_instance

/-- Posterior for the one-draw marginal kernel: almost everywhere the candidate posterior
kernel. This restates `posterior_gaussianLikelihood_gaussianReal` through the marginal
kernel. -/
theorem posterior_marginalGaussianKernel (m₀ : ℝ) {v₀ v : ℝ≥0} [NeZero v₀] [NeZero v] :
    ∀ᵐ x ∂(marginalGaussianKernel v ∘ₘ gaussianReal m₀ v₀),
      ((marginalGaussianKernel v)†(gaussianReal m₀ v₀)) x =
        normalPosteriorKernel m₀ v₀ v x := by
  have h₀ := NeZero.ne v₀
  have h := NeZero.ne v
  have hK : marginalGaussianKernel v = gaussianLikelihood v :=
    marginalGaussianKernel_eq_gaussianLikelihood h
  have : IsMarkovKernel (marginalGaussianKernel v) := by
    rw [hK]
    infer_instance
  have hKapply : ∀ θ, marginalGaussianKernel v θ = volume.withDensity (gaussianPDF θ v) :=
    fun θ => by rw [hK]; exact gaussianLikelihood_apply' h θ
  have hae := posterior_ae_eq_of_mul_eq (gaussianReal_of_var_ne_zero _ h₀)
    hKapply (measurable_gaussianPDF _ _) (measurable_gaussianPDF_mean v)
    (measurable_gaussianPDF _ _) (measurable_normalPostMean_gaussianPDF m₀ v₀ v)
    (fun _ ↦ lintegral_gaussianPDF_eq_one _ (normalPostVar_ne_zero h₀ h))
    (gaussianPDF_mul_gaussianPDF m₀ h₀ h)
  have hC : marginalGaussianKernel v ∘ₘ gaussianReal m₀ v₀ = gaussianReal m₀ (v₀ + v) := by
    rw [hK]
    exact gaussianLikelihood_comp_gaussianReal m₀ h₀ h
  rw [hC] at hae ⊢
  filter_upwards [hae] with x hx
  rw [hx, normalPosteriorKernel_apply m₀ h₀ h x,
    gaussianReal_of_var_ne_zero _ (normalPostVar_ne_zero h₀ h)]

/-- The one-draw marginal kernel has the same prior predictive law as the likelihood. -/
theorem marginalGaussianKernel_comp_gaussianReal (m₀ : ℝ) {v₀ v : ℝ≥0} (h₀ : v₀ ≠ 0)
    (h : v ≠ 0) :
    marginalGaussianKernel v ∘ₘ gaussianReal m₀ v₀ = gaussianReal m₀ (v₀ + v) := by
  rw [marginalGaussianKernel_eq_gaussianLikelihood h]
  exact gaussianLikelihood_comp_gaussianReal m₀ h₀ h

end Cslib.MachineLearning.Bayesian
