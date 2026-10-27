/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# Bayes' rule for densities

The prior is `μ = ν.withDensity p` and the likelihood kernel has densities, `κ θ = ρ.withDensity
(q θ)`. Suppose prior times likelihood factors as `p θ * q θ x = c x * r x θ`, where every `r x`
is a probability density with respect to `ν`. Completing the square for Gaussians is the typical
way to find such a factorization. Then:

* `comp_eq_withDensity_of_mul_eq`: the marginal law of the data (the evidence) is
  `ρ.withDensity c`;
* `compProd_eq_of_mul_eq`: the evidence and the kernel `x ↦ ν.withDensity (r x)` disintegrate the
  joint law;
* `posterior_ae_eq_of_mul_eq` (**Bayes' rule for densities**): for almost every observation `x`,
  Mathlib's posterior kernel `κ†μ` at `x` is `ν.withDensity (r x)`.

The posterior is determined only up to a null set of observations, so the conclusion is almost
everywhere, as in Mathlib's `ProbabilityTheory.ae_eq_posterior_of_compProd_eq`. For discrete
observations, `CSLibExt/MachineLearning/Bayesian/Basic.lean` gives the pointwise formula instead.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Bayesian

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
  {ν : Measure Θ} [SFinite ν] {ρ : Measure 𝓧} [SFinite ρ]
  {μ : Measure Θ} {κ : Kernel Θ 𝓧} {η : Kernel 𝓧 Θ}
  {p : Θ → ℝ≥0∞} {q : Θ → 𝓧 → ℝ≥0∞} {c : 𝓧 → ℝ≥0∞} {r : 𝓧 → Θ → ℝ≥0∞}

/-- **The evidence from a factorization of densities.** If the prior has density `p` with respect
to `ν`, the likelihood has density `q θ` with respect to `ρ`, and `p θ * q θ x = c x * r x θ` with
each `r x` a probability density, then the marginal law of the data has density `c`. -/
theorem comp_eq_withDensity_of_mul_eq (hμ : μ = ν.withDensity p)
    (hκ : ∀ θ, κ θ = ρ.withDensity (q θ)) (hp : Measurable p) (hq : Measurable (Function.uncurry q))
    (hc : Measurable c) (hr : Measurable (Function.uncurry r)) (hr1 : ∀ x, ∫⁻ θ, r x θ ∂ν = 1)
    (hfac : ∀ θ x, p θ * q θ x = c x * r x θ) :
    κ ∘ₘ μ = ρ.withDensity c := by
  have hκm : Measurable fun θ ↦ κ θ := κ.measurable
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), hμ,
    lintegral_withDensity_eq_lintegral_mul _ hp (κ.measurable_coe hs), withDensity_apply _ hs]
  have hm : Measurable (Function.uncurry fun θ x ↦ c x * r x θ) :=
    (hc.comp measurable_snd).mul (hr.comp measurable_swap)
  calc ∫⁻ θ, (p * fun θ ↦ κ θ s) θ ∂ν
      = ∫⁻ θ, ∫⁻ x in s, p θ * q θ x ∂ρ ∂ν := by
        refine lintegral_congr fun θ ↦ ?_
        have hqθ : Measurable fun x ↦ q θ x := hq.comp measurable_prodMk_left
        rw [Pi.mul_apply, hκ θ, withDensity_apply _ hs, lintegral_const_mul _ hqθ]
    _ = ∫⁻ θ, ∫⁻ x in s, c x * r x θ ∂ρ ∂ν := by simp_rw [hfac]
    _ = ∫⁻ x in s, ∫⁻ θ, c x * r x θ ∂ν ∂ρ := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ x in s, c x ∂ρ := by
        refine lintegral_congr fun x ↦ ?_
        have hrx : Measurable fun θ ↦ r x θ := hr.comp measurable_prodMk_left
        rw [lintegral_const_mul _ hrx, hr1, mul_one]

/-- Under the same factorization, the marginal `ρ.withDensity c` and the kernel `η` with densities
`r x` disintegrate the joint law of the data and the parameter. -/
theorem compProd_eq_of_mul_eq [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hμ : μ = ν.withDensity p)
    (hκ : ∀ θ, κ θ = ρ.withDensity (q θ)) (hη : ∀ x, η x = ν.withDensity (r x))
    (hp : Measurable p) (hq : Measurable (Function.uncurry q)) (hc : Measurable c)
    (hr : Measurable (Function.uncurry r)) (hr1 : ∀ x, ∫⁻ θ, r x θ ∂ν = 1)
    (hfac : ∀ θ x, p θ * q θ x = c x * r x θ) :
    (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply measurable_swap hs,
    Measure.compProd_apply (measurable_swap hs),
    comp_eq_withDensity_of_mul_eq hμ hκ hp hq hc hr hr1 hfac, hμ,
    lintegral_withDensity_eq_lintegral_mul _ hc (Kernel.measurable_kernel_prodMk_left hs),
    lintegral_withDensity_eq_lintegral_mul _ hp
      (Kernel.measurable_kernel_prodMk_left (measurable_swap hs))]
  have hind : Measurable (s.indicator fun _ ↦ (1 : ℝ≥0∞)) := measurable_const.indicator hs
  simp only [Pi.mul_apply]
  calc ∫⁻ x, c x * η x (Prod.mk x ⁻¹' s) ∂ρ
      = ∫⁻ x, ∫⁻ θ, s.indicator (fun _ ↦ 1) (x, θ) * (c x * r x θ) ∂ν ∂ρ := by
        congr 1
        funext x
        have hrx : Measurable fun θ ↦ r x θ := hr.comp measurable_prodMk_left
        rw [hη x, withDensity_apply _ (measurable_prodMk_left hs),
          ← lintegral_indicator (measurable_prodMk_left hs),
          ← lintegral_const_mul _ (hrx.indicator (measurable_prodMk_left hs))]
        congr 1
        funext θ
        by_cases hxθ : (x, θ) ∈ s <;> simp [hxθ]
    _ = ∫⁻ x, ∫⁻ θ, s.indicator (fun _ ↦ 1) (x, θ) * (p θ * q θ x) ∂ν ∂ρ := by
        simp_rw [hfac]
    _ = ∫⁻ θ, ∫⁻ x, s.indicator (fun _ ↦ 1) (x, θ) * (p θ * q θ x) ∂ρ ∂ν := by
        have h3 : Measurable fun z : 𝓧 × Θ ↦ s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (z.1, z.2) := by
          simp only [Prod.mk.eta]
          exact hind
        have h12 : Measurable fun z : 𝓧 × Θ ↦ p z.2 * q z.2 z.1 :=
          (hp.comp measurable_snd).mul (hq.comp measurable_swap)
        have hm : Measurable (Function.uncurry fun x θ ↦
            s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x, θ) * (p θ * q θ x)) := by
          simp only [Function.uncurry_def]
          exact h3.mul h12
        exact lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ θ, p θ * κ θ (Prod.mk θ ⁻¹' (Prod.swap ⁻¹' s)) ∂ν := by
        congr 1
        funext θ
        have hqθ : Measurable fun x ↦ q θ x := hq.comp measurable_prodMk_left
        rw [hκ θ, withDensity_apply _ (measurable_prodMk_left (measurable_swap hs)),
          ← lintegral_indicator (measurable_prodMk_left (measurable_swap hs)),
          ← lintegral_const_mul _ (hqθ.indicator (measurable_prodMk_left (measurable_swap hs)))]
        congr 1
        funext x
        by_cases hxθ : (x, θ) ∈ s <;> simp [hxθ]

/-- **Bayes' rule for densities.** If prior density times likelihood factors as
`p θ * q θ x = c x * r x θ` with each `r x` a probability density, then for almost every
observation `x` the posterior is `ν.withDensity (r x)`, and `c` is the density of the evidence
(`comp_eq_withDensity_of_mul_eq`). -/
theorem posterior_ae_eq_of_mul_eq [StandardBorelSpace Θ] [Nonempty Θ] [IsFiniteMeasure μ]
    [IsMarkovKernel κ] (hμ : μ = ν.withDensity p) (hκ : ∀ θ, κ θ = ρ.withDensity (q θ))
    (hp : Measurable p) (hq : Measurable (Function.uncurry q)) (hc : Measurable c)
    (hr : Measurable (Function.uncurry r)) (hr1 : ∀ x, ∫⁻ θ, r x θ ∂ν = 1)
    (hfac : ∀ θ x, p θ * q θ x = c x * r x θ) :
    ∀ᵐ x ∂(κ ∘ₘ μ), (κ†μ) x = ν.withDensity (r x) := by
  have hη : ∀ x, (Kernel.const 𝓧 ν).withDensity r x = ν.withDensity (r x) := fun x ↦ by
    rw [Kernel.withDensity_apply _ hr, Kernel.const_apply]
  have : IsMarkovKernel ((Kernel.const 𝓧 ν).withDensity r) :=
    ⟨fun x ↦ ⟨by rw [hη, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hr1]⟩⟩
  filter_upwards [ae_eq_posterior_of_compProd_eq
    (compProd_eq_of_mul_eq hμ hκ hη hp hq hc hr hr1 hfac)] with x hx
  rw [← hx, hη]

end Cslib.MachineLearning.Bayesian
