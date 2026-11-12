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

/-! # Normal-normal posterior, one-draw marginal form

The one-draw marginal law coincides with the Gaussian likelihood. The posterior below is a
restatement of the normal-normal posterior for that marginal law; its kernel and evidence
are the likelihood's own (no separate posterior object is constructed). -/

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

/-- **Normal-Normal posterior, marginal form.** Under a `N(m₀, v₀)` prior with `v₀ ≠ 0` and
noise variance `v ≠ 0`, the a.e. posterior restatement for the one-draw marginal law is the
candidate posterior kernel. This is `posterior_gaussianLikelihood_gaussianReal` applied to the
one-observation marginal; no new posterior kernel or evidence object is constructed. -/
theorem posterior_gaussianMarginalLaw_one (m₀ : ℝ) {v₀ v : ℝ≥0} [NeZero v₀] [NeZero v] :
    ∀ᵐ x ∂(gaussianLikelihood v ∘ₘ gaussianReal m₀ v₀),
      ((gaussianLikelihood v)†(gaussianReal m₀ v₀)) x =
        normalPosteriorKernel m₀ v₀ v x := by
  have h₀ : v₀ ≠ 0 := NeZero.ne v₀
  have h : v ≠ 0 := NeZero.ne v
  rw [gaussianLikelihood_comp_gaussianReal m₀ h₀ h]
  have hac : gaussianReal m₀ (v₀ + v) ≪ volume :=
    gaussianReal_absolutelyContinuous m₀ (by positivity)
  have hae := hac (posterior_gaussianLikelihood_gaussianReal m₀ (v₀ := v₀) (v := v))
  filter_upwards [hae] with x hx
  rw [hx, normalPosteriorKernel_apply m₀ h₀ h x]

end Cslib.MachineLearning.Bayesian
