/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Bayes' rule for discrete observations

A Bayesian model has a prior `μ` on a parameter space `Θ` and a likelihood, a Markov kernel
`κ : Kernel Θ 𝓧` giving the law of the data for each parameter. Mathlib defines the posterior
`κ†μ : Kernel 𝓧 Θ` abstractly, by disintegrating the joint law (`ProbabilityTheory.posterior`).
This file proves the textbook formula for it when the data are discrete.

* `bayesPosterior κ μ x`: the prior reweighted by the likelihood `θ ↦ κ θ {x}` of the observation
  and normalized by the evidence `(κ ∘ₘ μ) {x} = ∫ κ θ {x} dμ` (`comp_apply_singleton`).
* `posterior_eq_bayesPosterior` (**Bayes' rule**): for a countable observation space, `κ†μ x` is
  `bayesPosterior κ μ x` at every observation of positive evidence. The proof checks that the
  normalized measures disintegrate the joint law (`compProd_bayesKernel`) and uses Mathlib's
  uniqueness of the posterior (`ProbabilityTheory.ae_eq_posterior_of_compProd_eq`).
* `posterior_apply_singleton`: for countably many hypotheses, the posterior probability of `θ` is
  `μ {θ} * κ θ {x} / ∑ θ', μ {θ'} * κ θ' {x}`.
* `IsMLE`, `IsMAP`: maximum-likelihood hypotheses for a countable observation space, and maximum
  a posteriori hypotheses when the parameter space is countable too. `isMAP_iff`: a MAP
  hypothesis maximizes prior times likelihood. `isMAP_iff_isMLE_of_uniform`: under a uniform
  prior the two coincide. `isMAP_iff_posterior` restates MAP through Mathlib's posterior kernel.

The tests work through the base-rate example: a test with 90% sensitivity and a 5% false-positive
rate, for a condition with 1% prevalence, gives posterior probability `2/13` after a positive
result, and the MAP and maximum-likelihood diagnoses differ.

Mathlib's `Probability/Decision/BayesEstimator.lean` treats Bayes estimators for general losses
through the same posterior kernel, and Casella–Berger, Chapter 1 (`FormalizedTextbooks`) proves
Bayes' rule for a countable partition of events. The maximum-likelihood estimators of
`MathlibExt/Probability/Statistics/Likelihood.lean` are for families of densities and i.i.d.
samples; `IsMLE` here is the single-observation notion used to compare with MAP.

## References

* K. P. Murphy, *Probabilistic Machine Learning: An Introduction*, MIT Press, 2022, Chapters 2
  and 4.
* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §1.2.3.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Bayesian

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- **Bayes posterior.** Let $\kappa$ be a kernel from a measurable space $\Theta$ of hypotheses to
a measurable space $\mathcal X$ of observations (the likelihood) and $\mu$ a measure on $\Theta$
(the prior). The Bayes posterior after observing $x \in \mathcal X$ is the measure $\pi_x$ on
$\Theta$ with
$$\pi_x(s) = E(x)^{-1} \int_s \kappa_\theta(\{x\}) \, d\mu(\theta)$$
for every measurable $s \subseteq \Theta$, where $E(x) = (\kappa \circ \mu)(\{x\})$ is the evidence
of $x$: the mass of $\{x\}$ under the composition $\kappa \circ \mu$ of $\mu$ with $\kappa$, the
marginal law of the observation. The inverse is taken in $[0, \infty]$, with $0^{-1} = \infty$,
$\infty^{-1} = 0$ and $\infty \cdot 0 = 0$; in particular $\pi_x$ is the zero measure when the
evidence is zero. -/
noncomputable def bayesPosterior (κ : Kernel Θ 𝓧) (μ : Measure Θ) (x : 𝓧) : Measure Θ :=
  ((κ ∘ₘ μ) {x})⁻¹ • μ.withDensity fun θ ↦ κ θ {x}

/-- **The evidence is the integral of the likelihood.** Let $\kappa$ be a kernel from a measurable
space $\Theta$ to a measurable space $\mathcal X$ with measurable singletons, and $\mu$ a measure on
$\Theta$. For every $x \in \mathcal X$,
$$(\kappa \circ \mu)(\{x\}) = \int_\Theta \kappa_\theta(\{x\}) \, d\mu(\theta),$$
where $\kappa \circ \mu$ is the composition of $\mu$ with $\kappa$ (the marginal law of the
observation) and the right side is the Lebesgue integral of a $[0, \infty]$-valued function. -/
theorem comp_apply_singleton [MeasurableSingletonClass 𝓧] (κ : Kernel Θ 𝓧) (μ : Measure Θ)
    (x : 𝓧) : (κ ∘ₘ μ) {x} = ∫⁻ θ, κ θ {x} ∂μ :=
  Measure.bind_apply (measurableSet_singleton x) κ.aemeasurable

theorem withDensity_univ_eq_comp [MeasurableSingletonClass 𝓧] (κ : Kernel Θ 𝓧) (μ : Measure Θ)
    (x : 𝓧) : (μ.withDensity fun θ ↦ κ θ {x}) Set.univ = (κ ∘ₘ μ) {x} := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, comp_apply_singleton]

theorem bayesPosterior_apply (κ : Kernel Θ 𝓧) (μ : Measure Θ) (x : 𝓧) {s : Set Θ}
    (hs : MeasurableSet s) :
    bayesPosterior κ μ x s = ((κ ∘ₘ μ) {x})⁻¹ * ∫⁻ θ in s, κ θ {x} ∂μ := by
  rw [bayesPosterior, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul]

/-- **Evidence times posterior is the joint mass.** Let $\mathcal X$ be a measurable space with
measurable singletons, $\kappa$ a Markov kernel from a measurable space $\Theta$ to $\mathcal X$
and $\mu$ a finite measure on $\Theta$. Let $x \in \mathcal X$ and write $\pi_x$ for the Bayes
posterior of $\mu$ after observing $x$ under $\kappa$. Then for every measurable set
$s \subseteq \Theta$,
$$(\kappa \circ \mu)(\{x\}) \cdot \pi_x(s) = \int_s \kappa_\theta(\{x\}) \, d\mu(\theta),$$
where $\kappa \circ \mu$ is the composition of $\mu$ with $\kappa$, so that the first factor is the
evidence of $x$. -/
theorem comp_mul_bayesPosterior [MeasurableSingletonClass 𝓧] (κ : Kernel Θ 𝓧) [IsMarkovKernel κ]
    (μ : Measure Θ) [IsFiniteMeasure μ] (x : 𝓧) {s : Set Θ} (hs : MeasurableSet s) :
    (κ ∘ₘ μ) {x} * bayesPosterior κ μ x s = ∫⁻ θ in s, κ θ {x} ∂μ := by
  rw [bayesPosterior_apply κ μ x hs, ← mul_assoc]
  by_cases h0 : (κ ∘ₘ μ) {x} = 0
  · have hle : ∫⁻ θ in s, κ θ {x} ∂μ ≤ (κ ∘ₘ μ) {x} := by
      rw [comp_apply_singleton]
      exact setLIntegral_le_lintegral s _
    rw [h0] at hle ⊢
    simp [le_zero_iff.mp hle]
  · rw [ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]

theorem isProbabilityMeasure_bayesPosterior [MeasurableSingletonClass 𝓧] (κ : Kernel Θ 𝓧)
    [IsMarkovKernel κ] (μ : Measure Θ) [IsFiniteMeasure μ] {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) :
    IsProbabilityMeasure (bayesPosterior κ μ x) := by
  constructor
  rw [bayesPosterior_apply κ μ x MeasurableSet.univ, Measure.restrict_univ,
    ← comp_apply_singleton, ENNReal.inv_mul_cancel hx (measure_ne_top _ _)]

theorem bayesPosterior_univ_le_one [MeasurableSingletonClass 𝓧] (κ : Kernel Θ 𝓧)
    [IsMarkovKernel κ] (μ : Measure Θ) [IsFiniteMeasure μ] (x : 𝓧) :
    bayesPosterior κ μ x Set.univ ≤ 1 := by
  by_cases hx : (κ ∘ₘ μ) {x} = 0
  · rw [bayesPosterior_apply κ μ x MeasurableSet.univ, Measure.restrict_univ,
      ← comp_apply_singleton, hx, mul_zero]
    exact zero_le_one
  · have := isProbabilityMeasure_bayesPosterior κ μ hx
    exact prob_le_one

/-! ### Maximum likelihood and maximum a posteriori

Both notions compare point masses. `κ θ {x}` is the probability of the observation `x` only when
the observation space is countable with measurable singletons, and the posterior mass of `{θ}`
is the posterior probability of `θ` only when the parameter space is too. (In a continuous space
every singleton can have probability zero, and every candidate would qualify.) The definitions
therefore require these instances even though their bodies do not use them. Maximum likelihood
needs only discrete data: the parameter space is arbitrary, e.g. `[0, 1]` for Bernoulli data. -/

/-- **Maximum-likelihood hypothesis for a discrete observation.** Let $\kappa$ be a kernel from a
parameter space $\Theta$ to a countable observation space $\mathcal X$ with measurable singletons,
assigning to each hypothesis $\theta$ a measure $\kappa_\theta$ on $\mathcal X$. A hypothesis
$\theta \in \Theta$ is a maximum-likelihood hypothesis for the observation $x \in \mathcal X$ when
no hypothesis gives $x$ higher likelihood: $\kappa_{\theta'}(\{x\}) \le \kappa_\theta(\{x\})$ for
every $\theta' \in \Theta$. -/
@[nolint unusedArguments]
def IsMLE [Countable 𝓧] [MeasurableSingletonClass 𝓧] (κ : Kernel Θ 𝓧) (x : 𝓧) (θ : Θ) : Prop :=
  ∀ θ', κ θ' {x} ≤ κ θ {x}

/-- **Maximum a posteriori hypothesis.** Let $\Theta$ and $\mathcal X$ be countable measurable
spaces with measurable singletons, $\kappa$ a kernel from $\Theta$ to $\mathcal X$ and $\mu$ a
measure on $\Theta$, and write $\pi_x$ for the Bayes posterior of the prior $\mu$ after observing
$x \in \mathcal X$ under the likelihood $\kappa$. A hypothesis $\theta \in \Theta$ is a maximum a
posteriori (MAP) hypothesis for $x$ when $\pi_x(\{\theta'\}) \le \pi_x(\{\theta\})$ for every
$\theta' \in \Theta$. -/
@[nolint unusedArguments]
def IsMAP [Countable Θ] [MeasurableSingletonClass Θ] [Countable 𝓧] [MeasurableSingletonClass 𝓧]
    (κ : Kernel Θ 𝓧) (μ : Measure Θ) (x : 𝓧) (θ : Θ) : Prop :=
  ∀ θ', bayesPosterior κ μ x {θ'} ≤ bayesPosterior κ μ x {θ}

variable [Countable 𝓧] [MeasurableSingletonClass 𝓧]

/-- **Bayes posterior kernel.** Let $\mathcal X$ be a countable measurable space with measurable
singletons, $\kappa$ a kernel from a measurable space $\Theta$ to $\mathcal X$, and $\mu$ a measure
on $\Theta$. The Bayes posterior kernel is the kernel from $\mathcal X$ to $\Theta$ that sends each
observation $x \in \mathcal X$ to the Bayes posterior of the prior $\mu$ after observing $x$ under
the likelihood $\kappa$. -/
noncomputable def bayesKernel (κ : Kernel Θ 𝓧) (μ : Measure Θ) : Kernel 𝓧 Θ :=
  Kernel.ofFunOfCountable (bayesPosterior κ μ)

instance (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (μ : Measure Θ) [IsFiniteMeasure μ] :
    IsFiniteKernel (bayesKernel κ μ) :=
  ⟨⟨1, ENNReal.one_lt_top, fun x ↦ bayesPosterior_univ_le_one κ μ x⟩⟩

theorem compProd_bayesKernel (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (μ : Measure Θ)
    [IsFiniteMeasure μ] : (κ ∘ₘ μ) ⊗ₘ bayesKernel κ μ = (μ ⊗ₘ κ).map Prod.swap := by
  ext s hs
  rw [Measure.compProd_apply hs, lintegral_countable', Measure.map_apply measurable_swap hs,
    Measure.compProd_apply (measurable_swap hs)]
  have hsec : ∀ θ, κ θ (Prod.mk θ ⁻¹' (Prod.swap ⁻¹' s)) =
      ∑' x, (Prod.mk x ⁻¹' s).indicator (fun θ' ↦ κ θ' {x}) θ := by
    intro θ
    rw [← Measure.tsum_indicator_apply_singleton (κ θ) _ (Set.to_countable _).measurableSet]
    congr 1
  simp_rw [hsec]
  rw [lintegral_tsum fun x ↦ ((κ.measurable_coe (measurableSet_singleton x)).indicator
    (measurable_prodMk_left hs)).aemeasurable]
  refine tsum_congr fun x ↦ ?_
  rw [lintegral_indicator (measurable_prodMk_left hs), bayesKernel,
    Kernel.ofFunOfCountable, Kernel.coe_mk, mul_comm,
    comp_mul_bayesPosterior κ μ x (measurable_prodMk_left hs)]

section Posterior

variable [StandardBorelSpace Θ] [Nonempty Θ]

/-- **Bayes' rule for discrete observations.** Let the parameter space $\Theta$ be a nonempty
standard Borel space and the observation space $\mathcal X$ be countable with measurable
singletons. Let $\kappa$ be a Markov kernel from $\Theta$ to $\mathcal X$ (the likelihood),
writing $\kappa_\theta$ for the probability measure it assigns to $\theta \in \Theta$, let $\mu$
be a finite measure on $\Theta$ (the prior), and let $\kappa^\dagger\mu$ be Mathlib's posterior
kernel from $\mathcal X$ to $\Theta$. If the observation $x \in \mathcal X$ has nonzero evidence
$(\kappa \circ \mu)(\{x\})$, where $\kappa \circ \mu$ is the law of the observation under the
prior, then the posterior measure $\kappa^\dagger\mu(x)$ equals the Bayes posterior after
observing $x$: the prior $\mu$ reweighted by the likelihood $\theta \mapsto \kappa_\theta(\{x\})$
and divided by the evidence. -/
theorem posterior_eq_bayesPosterior (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (μ : Measure Θ)
    [IsFiniteMeasure μ] {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) :
    (κ†μ) x = bayesPosterior κ μ x := by
  have h := ae_eq_posterior_of_compProd_eq (compProd_bayesKernel κ μ)
  exact ((ae_iff_of_countable.mp h) x hx).symm

end Posterior

/-! ### Finitely or countably many hypotheses -/

section Countable

variable [Countable Θ] [MeasurableSingletonClass Θ]

omit [Countable 𝓧] in
/-- **The evidence as a sum over hypotheses.** Let $\Theta$ be a countable measurable space and
$\mathcal X$ a measurable space, both with measurable singletons, let $\kappa$ be a kernel from
$\Theta$ to $\mathcal X$ and $\mu$ a measure on $\Theta$. For every $x \in \mathcal X$,
$$(\kappa \circ \mu)(\{x\}) = \sum_{\theta \in \Theta} \mu(\{\theta\}) \, \kappa_\theta(\{x\}),$$
where $\kappa \circ \mu$ is the composition of $\mu$ with $\kappa$ (the marginal law of the
observation) and the sum is taken in $[0, \infty]$. -/
theorem comp_apply_singleton_eq_tsum (κ : Kernel Θ 𝓧) (μ : Measure Θ) (x : 𝓧) :
    (κ ∘ₘ μ) {x} = ∑' θ, μ {θ} * κ θ {x} := by
  rw [comp_apply_singleton, lintegral_countable']
  exact tsum_congr fun θ ↦ mul_comm _ _

omit [Countable 𝓧] in
/-- **Bayes' rule for countably many hypotheses.** Let $\Theta$ be a countable measurable space and
$\mathcal X$ a measurable space, both with measurable singletons, let $\kappa$ be a kernel from
$\Theta$ to $\mathcal X$ (the likelihood) and $\mu$ a measure on $\Theta$ (the prior). For every
observation $x \in \mathcal X$ and every $\theta \in \Theta$, the Bayes posterior $\pi_x$ of $\mu$
after observing $x$ satisfies
$$\pi_x(\{\theta\}) = \frac{\mu(\{\theta\}) \, \kappa_\theta(\{x\})}
{\sum_{\theta' \in \Theta} \mu(\{\theta'\}) \, \kappa_{\theta'}(\{x\})},$$
where the quotient is taken in $[0, \infty]$ with $0 / 0 = 0$ and $a / \infty = 0$ for every $a$.
The denominator is the evidence of $x$. -/
theorem bayesPosterior_apply_singleton (κ : Kernel Θ 𝓧) (μ : Measure Θ) (x : 𝓧) (θ : Θ) :
    bayesPosterior κ μ x {θ} = μ {θ} * κ θ {x} / ∑' θ', μ {θ'} * κ θ' {x} := by
  rw [bayesPosterior_apply κ μ x (measurableSet_singleton θ),
    lintegral_singleton' (κ.measurable_coe (measurableSet_singleton x)),
    comp_apply_singleton_eq_tsum, div_eq_mul_inv, mul_comm, mul_comm (κ θ {x})]

variable [StandardBorelSpace Θ] [Nonempty Θ]

/-- **Bayes' rule for Mathlib's posterior kernel with countably many hypotheses and
observations.** Let the parameter space $\Theta$ be a nonempty countable standard Borel space and
the observation space $\mathcal X$ be countable, both with measurable singletons. Let $\kappa$ be
a Markov kernel from $\Theta$ to $\mathcal X$ (the likelihood), writing $\kappa_\theta$ for the
probability measure it assigns to $\theta \in \Theta$, let $\mu$ be a finite measure on $\Theta$
(the prior), and let $\kappa^\dagger\mu$ be Mathlib's posterior kernel from $\mathcal X$ to
$\Theta$. If the observation $x \in \mathcal X$ has nonzero evidence $(\kappa \circ \mu)(\{x\})$,
where $\kappa \circ \mu$ is the law of the observation under the prior, then for every
$\theta \in \Theta$

$$
\kappa^\dagger\mu(x)(\{\theta\}) = \frac{\mu(\{\theta\})\,\kappa_\theta(\{x\})}
{\sum_{\theta' \in \Theta} \mu(\{\theta'\})\,\kappa_{\theta'}(\{x\})}.
$$
-/
theorem posterior_apply_singleton (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (μ : Measure Θ)
    [IsFiniteMeasure μ] {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (θ : Θ) :
    (κ†μ) x {θ} = μ {θ} * κ θ {x} / ∑' θ', μ {θ'} * κ θ' {x} := by
  rw [posterior_eq_bayesPosterior κ μ hx, bayesPosterior_apply_singleton]

end Countable

/-! ### MAP versus maximum likelihood -/

section Estimators

variable [Countable Θ] [MeasurableSingletonClass Θ]

/-- **MAP hypotheses maximize prior times likelihood.** Let $\Theta$ and $\mathcal X$ be countable
measurable spaces with measurable singletons, $\kappa$ a Markov kernel from $\Theta$ to
$\mathcal X$, $\mu$ a finite measure on $\Theta$, and $x \in \mathcal X$ an observation with
$(\kappa \circ \mu)(\{x\}) \neq 0$, where $\kappa \circ \mu$ is the composition of $\mu$ with
$\kappa$. Then $\theta \in \Theta$ is a MAP hypothesis for $x$ under the prior $\mu$ and the
likelihood $\kappa$ if and only if
$\mu(\{\theta'\}) \, \kappa_{\theta'}(\{x\}) \le \mu(\{\theta\}) \, \kappa_\theta(\{x\})$ for every
$\theta' \in \Theta$.

The evidence $(\kappa \circ \mu)(\{x\})$ is a common factor of all posterior masses. -/
theorem isMAP_iff (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (μ : Measure Θ) [IsFiniteMeasure μ]
    {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (θ : Θ) :
    IsMAP κ μ x θ ↔ ∀ θ', μ {θ'} * κ θ' {x} ≤ μ {θ} * κ θ {x} := by
  have hne : ∑' θ', μ {θ'} * κ θ' {x} ≠ 0 := by rwa [← comp_apply_singleton_eq_tsum]
  have hnt : ∑' θ', μ {θ'} * κ θ' {x} ≠ ⊤ := by
    rw [← comp_apply_singleton_eq_tsum]; exact measure_ne_top _ _
  simp only [IsMAP, bayesPosterior_apply_singleton, div_eq_mul_inv,
    ENNReal.mul_le_mul_iff_left (ENNReal.inv_ne_zero.mpr hnt) (ENNReal.inv_ne_top.mpr hne)]

/-- **Under a uniform prior, MAP is maximum likelihood.** Let $\Theta$ and $\mathcal X$ be countable
measurable spaces with measurable singletons, $\kappa$ a Markov kernel from $\Theta$ to
$\mathcal X$, and $\mu$ a finite measure on $\Theta$ that is uniform: there is $c \in [0, \infty]$,
$c \neq 0$, with $\mu(\{\theta\}) = c$ for every $\theta \in \Theta$. Let $x \in \mathcal X$ be an
observation with $(\kappa \circ \mu)(\{x\}) \neq 0$, where $\kappa \circ \mu$ is the composition of
$\mu$ with $\kappa$. Then a hypothesis $\theta \in \Theta$ is a MAP hypothesis for $x$ under the
prior $\mu$ and the likelihood $\kappa$ if and only if it is a maximum-likelihood hypothesis for
$x$ under $\kappa$. -/
theorem isMAP_iff_isMLE_of_uniform (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (μ : Measure Θ)
    [IsFiniteMeasure μ] {c : ℝ≥0∞} (hμ : ∀ θ, μ {θ} = c) (hc : c ≠ 0) {x : 𝓧}
    (hx : (κ ∘ₘ μ) {x} ≠ 0) (θ : Θ) : IsMAP κ μ x θ ↔ IsMLE κ x θ := by
  have hct : c ≠ ⊤ := by rw [← hμ θ]; exact measure_ne_top _ _
  simp only [isMAP_iff κ μ hx, hμ, IsMLE, ENNReal.mul_le_mul_iff_right hc hct]

variable [StandardBorelSpace Θ] [Nonempty Θ]

/-- **MAP hypotheses through the posterior kernel.** Let $\Theta$ be a nonempty countable standard
Borel space, $\mathcal X$ a countable measurable space with measurable singletons, $\kappa$ a Markov
kernel from $\Theta$ to $\mathcal X$, $\mu$ a finite measure on $\Theta$, and $x \in \mathcal X$ an
observation with $(\kappa \circ \mu)(\{x\}) \neq 0$, where $\kappa \circ \mu$ is the composition of
$\mu$ with $\kappa$. Write $\kappa^\dagger_\mu$ for the posterior kernel from $\mathcal X$ to
$\Theta$, the fixed disintegration of the joint law of hypothesis and observation along the
observation. Then $\theta \in \Theta$ is a MAP hypothesis for $x$ under the prior $\mu$ and the
likelihood $\kappa$ if and only if
$\kappa^\dagger_\mu(x)(\{\theta'\}) \le \kappa^\dagger_\mu(x)(\{\theta\})$ for every
$\theta' \in \Theta$. -/
theorem isMAP_iff_posterior (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (μ : Measure Θ)
    [IsFiniteMeasure μ] {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (θ : Θ) :
    IsMAP κ μ x θ ↔ ∀ θ', (κ†μ) x {θ'} ≤ (κ†μ) x {θ} := by
  rw [posterior_eq_bayesPosterior κ μ hx]
  rfl

end Estimators

end Cslib.MachineLearning.Bayesian
