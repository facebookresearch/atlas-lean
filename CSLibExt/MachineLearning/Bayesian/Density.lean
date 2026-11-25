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

/-- **The evidence from a factorization of densities.** Let $\nu$ be an s-finite measure on a
measurable space $\Theta$ and $\rho$ an s-finite measure on a measurable space $\mathcal{X}$. Let
$p : \Theta \to [0, \infty]$, $q : \Theta \times \mathcal{X} \to [0, \infty]$,
$c : \mathcal{X} \to [0, \infty]$ and $r : \mathcal{X} \times \Theta \to [0, \infty]$ be measurable
functions such that $\int r(x, \theta) \, d\nu(\theta) = 1$ for every $x \in \mathcal{X}$ and
$p(\theta) \, q(\theta, x) = c(x) \, r(x, \theta)$ for all $\theta \in \Theta$ and
$x \in \mathcal{X}$. If the prior $\mu$ is the measure on $\Theta$ with density $p$ with respect
to $\nu$, and the likelihood $\kappa$ is a kernel from $\Theta$ to $\mathcal{X}$ such that each
$\kappa(\theta)$ has density $q(\theta, \cdot)$ with respect to $\rho$, then the marginal law of
the data, the measure $\kappa \circ \mu$ on $\mathcal{X}$ given by
$(\kappa \circ \mu)(s) = \int \kappa(\theta)(s) \, d\mu(\theta)$ for measurable $s$, has density
$c$ with respect to $\rho$. -/
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

/-- **Disintegration of the joint law from a factorization of densities.** Let $\nu$ be an
s-finite measure on a measurable space $\Theta$ and $\rho$ an s-finite measure on a measurable
space $\mathcal{X}$. Let $p : \Theta \to [0, \infty]$,
$q : \Theta \times \mathcal{X} \to [0, \infty]$, $c : \mathcal{X} \to [0, \infty]$ and
$r : \mathcal{X} \times \Theta \to [0, \infty]$ be measurable functions such that
$\int r(x, \theta) \, d\nu(\theta) = 1$ for every $x \in \mathcal{X}$ and
$p(\theta) \, q(\theta, x) = c(x) \, r(x, \theta)$ for all $\theta \in \Theta$ and
$x \in \mathcal{X}$. Let the prior $\mu$ be an s-finite measure on $\Theta$ with density $p$ with
respect to $\nu$, let the likelihood $\kappa$ be an s-finite kernel from $\Theta$ to $\mathcal{X}$
such that each $\kappa(\theta)$ has density $q(\theta, \cdot)$ with respect to $\rho$, and let
$\eta$ be an s-finite kernel from $\mathcal{X}$ to $\Theta$ such that each $\eta(x)$ has density
$r(x, \cdot)$ with respect to $\nu$. Write $\kappa \circ \mu$ for the marginal law of the data,
$(\kappa \circ \mu)(s) = \int \kappa(\theta)(s) \, d\mu(\theta)$, and $\mu \otimes \kappa$ for the
joint law on $\Theta \times \mathcal{X}$,
$(\mu \otimes \kappa)(t) = \int \kappa(\theta)(\{x : (\theta, x) \in t\}) \, d\mu(\theta)$, and
similarly $(\kappa \circ \mu) \otimes \eta$ on $\mathcal{X} \times \Theta$. Then
$(\kappa \circ \mu) \otimes \eta$ is the image of $\mu \otimes \kappa$ under the swap
$(\theta, x) \mapsto (x, \theta)$. -/
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

/-- **Bayes' rule for densities.** Let $\Theta$ be a nonempty standard Borel space, $\nu$ an
s-finite measure on $\Theta$ and $\rho$ an s-finite measure on a measurable space $\mathcal{X}$.
Let $p : \Theta \to [0, \infty]$, $q : \Theta \times \mathcal{X} \to [0, \infty]$,
$c : \mathcal{X} \to [0, \infty]$ and $r : \mathcal{X} \times \Theta \to [0, \infty]$ be measurable
functions such that $\int r(x, \theta) \, d\nu(\theta) = 1$ for every $x \in \mathcal{X}$ and
$p(\theta) \, q(\theta, x) = c(x) \, r(x, \theta)$ for all $\theta \in \Theta$ and
$x \in \mathcal{X}$. Let the prior $\mu$ be a finite measure on $\Theta$ with density $p$ with
respect to $\nu$, and let the likelihood $\kappa$ be a Markov kernel from $\Theta$ to
$\mathcal{X}$ such that each $\kappa(\theta)$ has density $q(\theta, \cdot)$ with respect to
$\rho$. Then for almost every $x$ with respect to the marginal law of the data
$\kappa \circ \mu$, given by $(\kappa \circ \mu)(s) = \int \kappa(\theta)(s) \, d\mu(\theta)$, the
posterior $\kappa^\dagger_\mu(x)$ of $\kappa$ with respect to $\mu$ is the measure with density
$r(x, \cdot)$ with respect to $\nu$. -/
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
