/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.Density
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Normal–Normal conjugacy with known variance

The mean `θ` of a Gaussian has a `N(m₀, v₀)` prior and one real observation is `x ~ N(θ, v)`, with
the noise variance `v` known (`gaussianLikelihood v`, the kernel `θ ↦ gaussianReal θ v`). Both
variances are positive.

* `gaussianPDFReal_mul_gaussianPDFReal` (**completing the square**): prior density times
  likelihood equals the `N(m₀, v₀ + v)` marginal density of `x` times the
  `N(normalPostMean m₀ v₀ v x, normalPostVar v₀ v)` density in `θ`.
* `gaussianLikelihood_comp_gaussianReal`: the marginal law of `x` is `N(m₀, v₀ + v)`.
* `posterior_gaussianLikelihood_gaussianReal` (**conjugacy**): for almost every `x`, Mathlib's
  posterior kernel `κ†μ` at `x` is the Gaussian with
  * mean `normalPostMean m₀ v₀ v x = (v m₀ + v₀ x) / (v₀ + v)`, and
  * variance `normalPostVar v₀ v = v₀ v / (v₀ + v)`.
  The proof feeds the completed square to Bayes' rule for densities
  (`posterior_ae_eq_of_mul_eq`).
* `inv_normalPostVar`: precisions add, `1 / normalPostVar = 1 / v₀ + 1 / v`.
  `normalPostMean_eq`: the posterior mean moves from `m₀` toward `x` by the gain `v₀ / (v₀ + v)`.
* `gaussianLikelihood_comp_posterior` (**posterior predictive**): the next observation is
  `N(normalPostMean m₀ v₀ v x, normalPostVar v₀ v + v)`.

This file treats one observation. For `n` i.i.d. observations the sample mean is sufficient and has
law `N(θ, v / n)`, so the same formulas apply with `v / n`; that reduction is not formalized here.

Casella–Berger §7.5.6, in
`FormalizedTextbooks/CasellaBergerStatisticalInference/Chapter7/GaussianHierarchy.lean`,
proves the marginal in the case `m₀ = 0`, `v = 1`, through Mathlib's
`gaussianReal_conv_gaussianReal`. The marginal here is a by-product of completing the square,
which the posterior needs anyway.

## References

* K. P. Murphy, *Probabilistic Machine Learning: An Introduction*, MIT Press, 2022, Chapter 3
  (Bayes' rule for Gaussians).
* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §2.3.6.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Bayesian

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

/-- **Posterior variance of the normal–normal model.** For variances $v_0, v \ge 0$, the posterior
variance is $\frac{v_0 v}{v_0 + v}$, taken to be $0$ when $v_0 = v = 0$. In the normal–normal model
with prior variance $v_0$ and known noise variance $v$, this is the variance of the posterior of the
mean after one observation. -/
noncomputable def normalPostVar (v₀ v : ℝ≥0) : ℝ≥0 := v₀ * v / (v₀ + v)

/-- **Posterior mean of the Normal–Normal model.** For a prior mean $m_0 \in \mathbb{R}$, a prior
variance $v_0 \ge 0$, a noise variance $v \ge 0$ and an observation $x \in \mathbb{R}$, the
posterior mean is $(v m_0 + v_0 x)/(v_0 + v)$, taken to be $0$ when $v_0 = v = 0$. When
$v_0 + v > 0$ it is the precision-weighted average of $m_0$ and $x$. -/
noncomputable def normalPostMean (m₀ : ℝ) (v₀ v : ℝ≥0) (x : ℝ) : ℝ :=
  (v * m₀ + v₀ * x) / (v₀ + v)

theorem normalPostVar_ne_zero {v₀ v : ℝ≥0} (h₀ : v₀ ≠ 0) (h : v ≠ 0) : normalPostVar v₀ v ≠ 0 := by
  unfold normalPostVar
  have : v₀ + v ≠ 0 := by positivity
  positivity

/-- **Posterior mean as a gain update.** Let $m_0, x \in \mathbb{R}$, $v_0 > 0$ and $v \ge 0$. The
posterior mean $(v m_0 + v_0 x)/(v_0 + v)$ equals $m_0 + \frac{v_0}{v_0 + v}(x - m_0)$: it moves
from the prior mean $m_0$ toward the observation $x$ by the gain $v_0/(v_0 + v)$. -/
theorem normalPostMean_eq (m₀ : ℝ) {v₀ v : ℝ≥0} (h₀ : v₀ ≠ 0) (x : ℝ) :
    normalPostMean m₀ v₀ v x = m₀ + v₀ / (v₀ + v) * (x - m₀) := by
  have : (0 : ℝ) < v₀ + v := by positivity
  unfold normalPostMean
  field_simp
  ring

/-- **Precisions add.** For variances $v_0, v > 0$, the posterior variance $s = v_0 v/(v_0 + v)$
satisfies $s^{-1} = v_0^{-1} + v^{-1}$. -/
theorem inv_normalPostVar {v₀ v : ℝ≥0} (h₀ : v₀ ≠ 0) (h : v ≠ 0) :
    (normalPostVar v₀ v)⁻¹ = v₀⁻¹ + v⁻¹ := by
  unfold normalPostVar
  field_simp
  ring

/-- **Completing the square.** Let $m_0, \theta, x \in \mathbb{R}$ and $v_0, v > 0$, and write
$\varphi_{\mu, s}(y) = (2 \pi s)^{-1/2} \exp(-(y - \mu)^2 / (2 s))$ for the density of the Gaussian
with mean $\mu$ and variance $s$. With $\mu(x) = (v m_0 + v_0 x)/(v_0 + v)$ and
$s = v_0 v/(v_0 + v)$,

$$
\varphi_{m_0, v_0}(\theta)\,\varphi_{\theta, v}(x) =
\varphi_{m_0, v_0 + v}(x)\,\varphi_{\mu(x), s}(\theta):
$$

the prior density at $\theta$ times the likelihood of $x$ is the marginal density of $x$ times the
posterior density at $\theta$. -/
theorem gaussianPDFReal_mul_gaussianPDFReal (m₀ : ℝ) {v₀ v : ℝ≥0} (h₀ : v₀ ≠ 0) (h : v ≠ 0)
    (θ x : ℝ) :
    gaussianPDFReal m₀ v₀ θ * gaussianPDFReal θ v x =
      gaussianPDFReal m₀ (v₀ + v) x *
        gaussianPDFReal (normalPostMean m₀ v₀ v x) (normalPostVar v₀ v) θ := by
  have hv₀ : (0 : ℝ) < v₀ := by positivity
  have hv : (0 : ℝ) < v := by positivity
  simp only [gaussianPDFReal, normalPostVar, normalPostMean, NNReal.coe_add, NNReal.coe_div,
    NNReal.coe_mul]
  conv_lhs => rw [mul_mul_mul_comm, ← Real.exp_add, ← mul_inv, ← Real.sqrt_mul (by positivity)]
  conv_rhs => rw [mul_mul_mul_comm, ← Real.exp_add, ← mul_inv, ← Real.sqrt_mul (by positivity)]
  congr 2
  · congr 1
    field_simp
  · field_simp
    ring

theorem gaussianPDF_mul_gaussianPDF (m₀ : ℝ) {v₀ v : ℝ≥0} (h₀ : v₀ ≠ 0) (h : v ≠ 0) (θ x : ℝ) :
    gaussianPDF m₀ v₀ θ * gaussianPDF θ v x =
      gaussianPDF m₀ (v₀ + v) x *
        gaussianPDF (normalPostMean m₀ v₀ v x) (normalPostVar v₀ v) θ := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    gaussianPDFReal_mul_gaussianPDFReal m₀ h₀ h]

/-! ### The Gaussian likelihood with known variance -/

/-- **Measurability of the Gaussian density in its mean and argument.** For a variance $v \ge 0$,
write $\varphi_{\theta, v}(x) = (2 \pi v)^{-1/2} \exp(-(x - \theta)^2 / (2 v))$ for the density
at $x$ of the Gaussian with mean $\theta$ and variance $v$, read as $0$ when $v = 0$, with values
in $[0, \infty]$. Then $(\theta, x) \mapsto \varphi_{\theta, v}(x)$ is a measurable map on
$\mathbb{R} \times \mathbb{R}$. -/
theorem measurable_gaussianPDF_mean (v : ℝ≥0) :
    Measurable (Function.uncurry fun θ x : ℝ ↦ gaussianPDF θ v x) :=
  measurable_uncurry_gaussianPDF.comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

/-- **Gaussian likelihood with known variance.** For a noise variance $v \ge 0$, the Gaussian
likelihood is the kernel from $\mathbb{R}$ to $\mathbb{R}$ that sends a parameter $\theta$ to the
law of the observation $x \sim N(\theta, v)$, the Gaussian with mean $\theta$ and variance $v$: for
$v > 0$ it is the measure with the $N(\theta, v)$ density with respect to Lebesgue measure, and for
$v = 0$ it is the point mass at $\theta$. -/
noncomputable def gaussianLikelihood (v : ℝ≥0) : Kernel ℝ ℝ :=
  if v = 0 then Kernel.deterministic id measurable_id
  else (Kernel.const ℝ volume).withDensity fun θ x ↦ gaussianPDF θ v x

theorem gaussianLikelihood_apply {v : ℝ≥0} (h : v ≠ 0) (θ : ℝ) :
    gaussianLikelihood v θ = gaussianReal θ v := by
  simp only [gaussianLikelihood, h, ↓reduceIte]
  rw [Kernel.withDensity_apply _ (measurable_gaussianPDF_mean v), Kernel.const_apply,
    gaussianReal_of_var_ne_zero _ h]

/-- **Noiseless Gaussian likelihood.** With noise variance $0$, the Gaussian likelihood sends each
$\theta \in \mathbb{R}$ to the Gaussian law with mean $\theta$ and variance $0$, which is the point
mass at $\theta$: the observation is the parameter. -/
theorem gaussianLikelihood_zero_apply (θ : ℝ) : gaussianLikelihood 0 θ = gaussianReal θ 0 := by
  simp [gaussianLikelihood, Kernel.deterministic_apply]

instance {v : ℝ≥0} : IsMarkovKernel (gaussianLikelihood v) := by
  by_cases h : v = 0
  · subst h
    exact ⟨fun θ ↦ by rw [gaussianLikelihood_zero_apply]; infer_instance⟩
  · exact ⟨fun θ ↦ by rw [gaussianLikelihood_apply h]; infer_instance⟩

theorem measurable_normalPostMean_gaussianPDF (m₀ : ℝ) (v₀ v : ℝ≥0) :
    Measurable (Function.uncurry fun x θ : ℝ ↦
      gaussianPDF (normalPostMean m₀ v₀ v x) (normalPostVar v₀ v) θ) := by
  have hf : Measurable fun a : ℝ × ℝ ↦ (normalPostMean m₀ v₀ v a.1, normalPostVar v₀ v, a.2) := by
    unfold normalPostMean
    fun_prop
  exact measurable_uncurry_gaussianPDF.comp hf

theorem gaussianLikelihood_apply' {v : ℝ≥0} (h : v ≠ 0) (θ : ℝ) :
    gaussianLikelihood v θ = volume.withDensity (gaussianPDF θ v) := by
  rw [gaussianLikelihood_apply h, gaussianReal_of_var_ne_zero _ h]

/-- **The marginal of the data.** Let $m_0 \in \mathbb{R}$ and $v_0, v > 0$, and write
$N(\mu, s)$ for the Gaussian law with mean $\mu$ and variance $s$. If the parameter $\theta$ has
prior $N(m_0, v_0)$ and the observation given $\theta$ has law $N(\theta, v)$ (the Gaussian
likelihood with noise variance $v$), then the marginal law of the observation is $N(m_0, v_0 + v)$.

Applied with the posterior in place of the prior, this also gives the posterior predictive law. -/
theorem gaussianLikelihood_comp_gaussianReal (m₀ : ℝ) {v₀ v : ℝ≥0} (h₀ : v₀ ≠ 0) (h : v ≠ 0) :
    gaussianLikelihood v ∘ₘ gaussianReal m₀ v₀ = gaussianReal m₀ (v₀ + v) := by
  rw [comp_eq_withDensity_of_mul_eq (gaussianReal_of_var_ne_zero _ h₀)
      (gaussianLikelihood_apply' h) (measurable_gaussianPDF _ _) (measurable_gaussianPDF_mean v)
      (measurable_gaussianPDF _ _) (measurable_normalPostMean_gaussianPDF m₀ v₀ v)
      (fun _ ↦ lintegral_gaussianPDF_eq_one _ (normalPostVar_ne_zero h₀ h))
      (gaussianPDF_mul_gaussianPDF m₀ h₀ h),
    gaussianReal_of_var_ne_zero _ (by positivity)]

/-! ### The posterior -/

/-- **Candidate posterior kernel of the normal–normal model.** Let $m_0 \in \mathbb{R}$ and
$v_0, v \ge 0$, let $s = \frac{v_0 v}{v_0 + v}$ be the posterior variance and, for
$x \in \mathbb{R}$, let $\mu(x) = \frac{v m_0 + v_0 x}{v_0 + v}$ be the posterior mean (with
$0 / 0 = 0$). The kernel from $\mathbb{R}$ to $\mathbb{R}$ sends $x$ to the measure with density
$\theta \mapsto \frac{1}{\sqrt{2 \pi s}} e^{-(\theta - \mu(x))^2 / (2 s)}$ with respect to Lebesgue
measure. For $v_0, v > 0$ this is the normal law $N(\mu(x), s)$. If $v_0 = 0$ or $v = 0$, then
$s = 0$, the density is taken to be $0$, and the kernel is the zero measure at every $x$. -/
noncomputable def normalPosteriorKernel (m₀ : ℝ) (v₀ v : ℝ≥0) : Kernel ℝ ℝ :=
  (Kernel.const ℝ volume).withDensity fun x θ ↦
    gaussianPDF (normalPostMean m₀ v₀ v x) (normalPostVar v₀ v) θ

theorem normalPosteriorKernel_apply (m₀ : ℝ) {v₀ v : ℝ≥0} (h₀ : v₀ ≠ 0) (h : v ≠ 0) (x : ℝ) :
    normalPosteriorKernel m₀ v₀ v x =
      gaussianReal (normalPostMean m₀ v₀ v x) (normalPostVar v₀ v) := by
  rw [normalPosteriorKernel,
    Kernel.withDensity_apply _ (measurable_normalPostMean_gaussianPDF m₀ v₀ v), Kernel.const_apply,
    gaussianReal_of_var_ne_zero _ (normalPostVar_ne_zero h₀ h)]

instance (m₀ : ℝ) (v₀ v : ℝ≥0) [NeZero v₀] [NeZero v] :
    IsMarkovKernel (normalPosteriorKernel m₀ v₀ v) :=
  ⟨fun x ↦ by
    rw [normalPosteriorKernel_apply m₀ (NeZero.ne v₀) (NeZero.ne v)]; infer_instance⟩

/-- **Disintegration of the Normal–Normal joint law.** Let $m_0 \in \mathbb{R}$ and $v_0, v > 0$,
and write $N(\mu, s)$ for the Gaussian law with mean $\mu$ and variance $s$. Let $\pi = N(m_0, v_0)$
be the prior on the parameter $\theta$, let $K$ be the Gaussian likelihood with noise variance $v$,
so that $K(\theta) = N(\theta, v)$, and let $Q$ be the normal posterior kernel,
$Q(x) = N(\mu(x), s)$ with $\mu(x) = (v m_0 + v_0 x)/(v_0 + v)$ and $s = v_0 v/(v_0 + v)$. For a
measure $\rho$ and a kernel $L$, write $L \circ \rho = \int L(y)\,d\rho(y)$ and $\rho \otimes L$ for
the law of $(y, z)$ when $y \sim \rho$ and $z \sim L(y)$. Then $(K \circ \pi) \otimes Q$ is the
image of $\pi \otimes K$ under $(\theta, x) \mapsto (x, \theta)$: the joint law of $(x, \theta)$ is
the marginal law $K \circ \pi$ of $x$ followed by the posterior kernel. -/
theorem compProd_normalPosteriorKernel (m₀ : ℝ) {v₀ v : ℝ≥0} [NeZero v₀] [NeZero v] :
    (gaussianLikelihood v ∘ₘ gaussianReal m₀ v₀) ⊗ₘ normalPosteriorKernel m₀ v₀ v =
      (gaussianReal m₀ v₀ ⊗ₘ gaussianLikelihood v).map Prod.swap := by
  have h₀ := NeZero.ne v₀
  have h := NeZero.ne v
  refine compProd_eq_of_mul_eq (gaussianReal_of_var_ne_zero _ h₀) (gaussianLikelihood_apply' h)
    (fun x ↦ ?_) (measurable_gaussianPDF _ _) (measurable_gaussianPDF_mean v)
    (measurable_gaussianPDF _ _) (measurable_normalPostMean_gaussianPDF m₀ v₀ v)
    (fun _ ↦ lintegral_gaussianPDF_eq_one _ (normalPostVar_ne_zero h₀ h))
    (gaussianPDF_mul_gaussianPDF m₀ h₀ h)
  rw [normalPosteriorKernel,
    Kernel.withDensity_apply _ (measurable_normalPostMean_gaussianPDF m₀ v₀ v), Kernel.const_apply]

/-- **Normal–Normal conjugacy with known variance.** Let $m_0 \in \mathbb{R}$ and $v_0, v > 0$. Take
the prior $N(m_0, v_0)$ on the mean $\theta$ and the likelihood under which an observation $x$ has
law $N(\theta, v)$. Then for Lebesgue-almost every $x \in \mathbb{R}$, the posterior distribution of
$\theta$ given $x$ is the normal law with mean $\frac{v m_0 + v_0 x}{v_0 + v}$ and variance
$\frac{v_0 v}{v_0 + v}$. -/
theorem posterior_gaussianLikelihood_gaussianReal (m₀ : ℝ) {v₀ v : ℝ≥0} [NeZero v₀] [NeZero v] :
    ∀ᵐ x, ((gaussianLikelihood v)†(gaussianReal m₀ v₀)) x =
      gaussianReal (normalPostMean m₀ v₀ v x) (normalPostVar v₀ v) := by
  have h₀ := NeZero.ne v₀
  have h := NeZero.ne v
  have hae := posterior_ae_eq_of_mul_eq (gaussianReal_of_var_ne_zero _ h₀)
    (gaussianLikelihood_apply' h) (measurable_gaussianPDF _ _) (measurable_gaussianPDF_mean v)
    (measurable_gaussianPDF _ _) (measurable_normalPostMean_gaussianPDF m₀ v₀ v)
    (fun _ ↦ lintegral_gaussianPDF_eq_one _ (normalPostVar_ne_zero h₀ h))
    (gaussianPDF_mul_gaussianPDF m₀ h₀ h)
  rw [gaussianLikelihood_comp_gaussianReal m₀ h₀ h] at hae
  filter_upwards [gaussianReal_absolutelyContinuous' m₀ (v := v₀ + v) (by positivity) hae]
    with x hx
  rw [hx, gaussianReal_of_var_ne_zero _ (normalPostVar_ne_zero h₀ h)]

/-- **Normal–Normal posterior predictive.** Let $m_0 \in \mathbb{R}$ and $v_0, v > 0$, and write
$N(\mu, s)$ for the Gaussian law with mean $\mu$ and variance $s$. Take the prior $N(m_0, v_0)$ on
the parameter $\theta$ and the Gaussian likelihood $\theta \mapsto N(\theta, v)$, and let
$\mu(x) = (v m_0 + v_0 x)/(v_0 + v)$ and $s = v_0 v/(v_0 + v)$. For Lebesgue-almost every
observation $x$, a new observation drawn from the likelihood, with $\theta$ distributed according
to the posterior given $x$, has law $N(\mu(x), s + v)$. -/
theorem gaussianLikelihood_comp_posterior (m₀ : ℝ) {v₀ v : ℝ≥0} [NeZero v₀] [NeZero v] :
    ∀ᵐ x, gaussianLikelihood v ∘ₘ ((gaussianLikelihood v)†(gaussianReal m₀ v₀)) x =
      gaussianReal (normalPostMean m₀ v₀ v x) (normalPostVar v₀ v + v) := by
  filter_upwards [posterior_gaussianLikelihood_gaussianReal m₀ (v₀ := v₀) (v := v)] with x hx
  rw [hx, gaussianLikelihood_comp_gaussianReal _
    (normalPostVar_ne_zero (NeZero.ne v₀) (NeZero.ne v)) (NeZero.ne v)]

end Cslib.MachineLearning.Bayesian
