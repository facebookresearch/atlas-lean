/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `bc0a5a31aa07d127ead55e6848aa133300c4ce0a`.
Original formalization by Manasa Hariharan (@manasahari-meta); ported with permission.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Moments.Variance

/-!
# Estimation risk: bias, mean squared error, and unbiasedness

Finite bias and finite mean squared error for a fixed real estimator under a
normalized probability law. Integrability evidence is an explicit input to the
finite declarations, so nonintegrable estimators have no finite source value.
A separately labeled extended bridge preserves infinite squared error.
Unbiasedness for a target function carries integrability inside the predicate.
Under a finite second moment, MSE decomposes into variance plus squared bias.

Source: Casella-Berger Definitions 7.3.1 and 7.3.2 with equation 7.3.1 and
section 7.3.2 (blueprints `af_723199a7ca6fb3e936a73618`,
`af_fd40353442120bd19166139d`, `af_95118d196fd6478105a6eb43`,
`af_3a1bafba0b7dff99554b01f0`). The estimator map is fixed before the law and
the target value; no parameter-dependent estimator map is accepted.
-/

namespace MathlibExt.Probability.Statistics.EstimationRisk

@[expose] public section

open MeasureTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- **Bias of an estimator.** Let $S$ be a measurable space, $W : S \to \mathbb{R}$ an estimator,
$\mu$ a probability measure on $S$ for which $W$ is integrable, and $\theta \in \mathbb{R}$ a
target. The bias of $W$ under $\mu$ at $\theta$ is $\int_S W \, d\mu - \theta$, the expected value
of $W$ under $\mu$ minus $\theta$.

Integrability of $W$ is part of the input: it is the domain on which the expectation exists in
the source (Chapter 2, Definition 2.2.1), so a nonintegrable estimator has no finite bias.

Source: blueprint `af_723199a7ca6fb3e936a73618`. -/
noncomputable def bias (W : S → ℝ) (μ : ProbabilityMeasure S) (θ : ℝ)
    (_hW : Integrable W (μ : Measure S)) : ℝ :=
  ∫ x, W x ∂(μ : Measure S) - θ

/-- **Bias as an integral.** Let $S$ be a measurable space, $W : S \to \mathbb{R}$ an estimator,
$\mu$ a probability measure on $S$ for which $W$ is integrable, and $\theta \in \mathbb{R}$ a
target. Then the bias of $W$ under $\mu$ at $\theta$ equals $\int_S W \, d\mu - \theta$.

Source: blueprint `af_723199a7ca6fb3e936a73618`. -/
@[simp]
theorem bias_eq_integral (W : S → ℝ) (μ : ProbabilityMeasure S) (θ : ℝ)
    (hW : Integrable W (μ : Measure S)) :
    bias W μ θ hW = ∫ x, W x ∂(μ : Measure S) - θ :=
  rfl

/-- **Mean squared error.** Let $\mu$ be a probability measure on a measurable space $S$, let
$W : S \to \mathbb{R}$ be an estimator and $\theta \in \mathbb{R}$ a target value, and suppose the
squared error $x \mapsto (W(x) - \theta)^2$ is $\mu$-integrable. The mean squared error of $W$ at
$\theta$ under $\mu$ is the real number $\int_S (W(x) - \theta)^2 \, d\mu(x)$.

The integrability hypothesis is part of the definition: without it no finite mean squared error is
defined.

Source: Casella–Berger, Definition 7.3.1; blueprint `af_fd40353442120bd19166139d`. -/
noncomputable def meanSquaredError (W : S → ℝ) (μ : ProbabilityMeasure S)
    (θ : ℝ)
    (_hW2 : Integrable (fun x => (W x - θ) ^ 2) (μ : Measure S)) : ℝ :=
  ∫ x, (W x - θ) ^ 2 ∂(μ : Measure S)

/-- **Mean squared error as an integral.** Let $\mu$ be a probability measure on a measurable
space $S$, let $W : S \to \mathbb{R}$ and $\theta \in \mathbb{R}$, and suppose the squared error
$x \mapsto (W(x) - \theta)^2$ is $\mu$-integrable. Then the mean squared error of $W$ at $\theta$
under $\mu$ equals $\int_S (W(x) - \theta)^2 \, d\mu(x)$.

Source: blueprint `af_fd40353442120bd19166139d`. -/
@[simp]
theorem meanSquaredError_eq_integral (W : S → ℝ) (μ : ProbabilityMeasure S)
    (θ : ℝ)
    (hW2 : Integrable (fun x => (W x - θ) ^ 2) (μ : Measure S)) :
    meanSquaredError W μ θ hW2 = ∫ x, (W x - θ) ^ 2 ∂(μ : Measure S) :=
  rfl

/-- **Extended mean squared error.** Let $\mu$ be a probability measure on a measurable space $S$,
let $W : S \to \mathbb{R}$ be an estimator and let $\theta \in \mathbb{R}$ be a target value. The
extended mean squared error of $W$ at $\theta$ under $\mu$ is the (lower) Lebesgue integral
$\int_S (W(x) - \theta)^2 \, d\mu(x)$ of the nonnegative squared error, computed in $[0, \infty]$.
It is defined for every $W$, with no integrability hypothesis.

When the squared error is $\mu$-integrable, this value is finite and equals the mean squared error;
when the squared error is almost everywhere strongly measurable but not $\mu$-integrable, it equals
$\infty$.

Source: blueprint `af_fd40353442120bd19166139d`. -/
noncomputable def meanSquaredErrorENN (W : S → ℝ) (μ : ProbabilityMeasure S)
    (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((W x - θ) ^ 2) ∂(μ : Measure S)

/-- **Finite and extended mean squared error agree.** Let $\mu$ be a probability measure on a
measurable space $S$, let $W : S \to \mathbb{R}$ and $\theta \in \mathbb{R}$, and suppose the
squared error $x \mapsto (W(x) - \theta)^2$ is $\mu$-integrable. Then the extended mean squared
error $\int_S (W(x) - \theta)^2 \, d\mu(x)$, computed in $[0, \infty]$, is finite and equals the
mean squared error of $W$ at $\theta$ under $\mu$.

Source: blueprint `af_fd40353442120bd19166139d`. -/
theorem ofReal_meanSquaredError {W : S → ℝ} {μ : ProbabilityMeasure S}
    {θ : ℝ}
    (h : Integrable (fun x => (W x - θ) ^ 2) (μ : Measure S)) :
    ENNReal.ofReal (meanSquaredError W μ θ h) = meanSquaredErrorENN W μ θ := by
  rw [meanSquaredError, meanSquaredErrorENN]
  exact ofReal_integral_eq_lintegral_ofReal h
    (Filter.Eventually.of_forall fun x => sq_nonneg (W x - θ))

/-- **Extended mean squared error of a measurable non-integrable squared error is infinite.** Let
$\mu$ be a probability measure on a measurable space $S$, $W : S \to \mathbb{R}$ an estimator and
$\theta \in \mathbb{R}$. If the squared error $x \mapsto (W(x) - \theta)^2$ is almost everywhere
strongly measurable with respect to $\mu$ but not $\mu$-integrable, then the extended mean squared
error $\int_S (W(x) - \theta)^2 \, d\mu(x) \in [0, \infty]$ of $W$ at $\theta$ equals $\infty$.

Source: blueprint `af_fd40353442120bd19166139d`. -/
theorem meanSquaredErrorENN_eq_top_of_not_finite {W : S → ℝ}
    {μ : ProbabilityMeasure S} {θ : ℝ}
    (hm : AEStronglyMeasurable (fun x => (W x - θ) ^ 2) (μ : Measure S))
    (h : ¬ Integrable (fun x => (W x - θ) ^ 2) (μ : Measure S)) :
    meanSquaredErrorENN W μ θ = ∞ := by
  have hfin : ¬ HasFiniteIntegral (fun x => (W x - θ) ^ 2) (μ : Measure S) :=
    fun hfin => h ⟨hm, hfin⟩
  rw [HasFiniteIntegral] at hfin
  have htop : ∫⁻ x, ‖(W x - θ) ^ 2‖ₑ ∂(μ : Measure S) = ∞ :=
    le_antisymm le_top (le_of_not_gt hfin)
  rw [meanSquaredErrorENN, ← htop]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact (Real.enorm_of_nonneg (sq_nonneg (W x - θ))).symm

/-- **Family bias of an estimator.** Let $S$ be a measurable space, $W : S \to \mathbb{R}$ an
estimator, $(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$ such that $W$
is integrable for every $P_\theta$, and $\tau : \Theta \to \mathbb{R}$ a target function. The
family bias of $W$ is the function on $\Theta$ whose value at $\theta$ is the bias of $W$ under
$P_\theta$ at the target $\tau(\theta)$, that is, $\int_S W \, dP_\theta - \tau(\theta)$.

The estimator $W$ is fixed before the family and does not depend on $\theta$.

Source: blueprint `af_723199a7ca6fb3e936a73618`. -/
noncomputable def familyBias {Θ : Type*} (W : S → ℝ)
    (P : Θ → ProbabilityMeasure S) (τ : Θ → ℝ)
    (h : ∀ θ, Integrable W ((P θ) : Measure S)) : Θ → ℝ :=
  fun θ => bias W (P θ) (τ θ) (h θ)

/-- **Family bias as an integral.** Let $S$ be a measurable space, $W : S \to \mathbb{R}$ an
estimator, $(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$ such that $W$
is integrable for every $P_\theta$, and $\tau : \Theta \to \mathbb{R}$ a target function. Then for
every $\theta \in \Theta$ the family bias of $W$ at $\theta$ equals
$\int_S W \, dP_\theta - \tau(\theta)$.

Source: blueprint `af_723199a7ca6fb3e936a73618`. -/
@[simp]
theorem familyBias_apply {Θ : Type*} (W : S → ℝ)
    (P : Θ → ProbabilityMeasure S) (τ : Θ → ℝ)
    (h : ∀ θ, Integrable W ((P θ) : Measure S)) (θ : Θ) :
    familyBias W P τ h θ = ∫ x, W x ∂((P θ) : Measure S) - τ θ :=
  rfl

/-- **Family mean squared error of an estimator.** Let $S$ be a measurable space,
$W : S \to \mathbb{R}$ an estimator, $(P_\theta)_{\theta \in \Theta}$ a family of probability
measures on $S$ and $\tau : \Theta \to \mathbb{R}$ a target function such that
$(W - \tau(\theta))^2$ is integrable for $P_\theta$ for every $\theta \in \Theta$. The family mean
squared error of $W$ is the function on $\Theta$ whose value at $\theta$ is the mean squared error
of $W$ under $P_\theta$ at the target $\tau(\theta)$, that is,
$\int_S (W(x) - \tau(\theta))^2 \, dP_\theta(x)$.

The estimator $W$ is fixed before the family and does not depend on $\theta$.

Source: blueprint `af_fd40353442120bd19166139d`. -/
noncomputable def familyMeanSquaredError {Θ : Type*} (W : S → ℝ)
    (P : Θ → ProbabilityMeasure S) (τ : Θ → ℝ)
    (h : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) ((P θ) : Measure S)) :
    Θ → ℝ :=
  fun θ => meanSquaredError W (P θ) (τ θ) (h θ)

/-- **Family mean squared error as an integral.** Let $S$ be a measurable space,
$W : S \to \mathbb{R}$ an estimator, $(P_\theta)_{\theta \in \Theta}$ a family of probability
measures on $S$ and $\tau : \Theta \to \mathbb{R}$ a target function such that
$(W - \tau(\theta))^2$ is integrable for $P_\theta$ for every $\theta \in \Theta$. Then for every
$\theta \in \Theta$ the family mean squared error of $W$ at $\theta$ equals
$\int_S (W(x) - \tau(\theta))^2 \, dP_\theta(x)$.

Source: blueprint `af_fd40353442120bd19166139d`. -/
@[simp]
theorem familyMeanSquaredError_apply {Θ : Type*} (W : S → ℝ)
    (P : Θ → ProbabilityMeasure S) (τ : Θ → ℝ)
    (h : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) ((P θ) : Measure S))
    (θ : Θ) :
    familyMeanSquaredError W P τ h θ =
      ∫ x, (W x - τ θ) ^ 2 ∂((P θ) : Measure S) :=
  rfl

/-- **Unbiased estimator.** Let $(P_\theta)_{\theta \in \Theta}$ be a family of probability measures
on a measurable space $S$ and $\tau : \Theta \to \mathbb{R}$ a target function. An estimator
$W : S \to \mathbb{R}$ is unbiased for $\tau$ if for every $\theta \in \Theta$ the function $W$ is
$P_\theta$-integrable and $\int_S W \, dP_\theta = \tau(\theta)$.

Integrability is part of the definition, so a non-integrable estimator is never unbiased. The
estimator $W$ is fixed and does not depend on $\theta$.

Source: Casella–Berger Definition 7.3.2 is the case $\tau(\theta) = \theta$ on real parameters;
the general target follows section 7.3.2. Blueprint `af_95118d196fd6478105a6eb43`. -/
def IsUnbiased {Θ : Type*} (W : S → ℝ) (P : Θ → ProbabilityMeasure S)
    (τ : Θ → ℝ) : Prop :=
  ∀ θ, Integrable W ((P θ) : Measure S) ∧
    ∫ x, W x ∂((P θ) : Measure S) = τ θ

/-- **Unbiased estimators are integrable.** Let $(P_\theta)_{\theta \in \Theta}$ be a family of
probability measures on $S$ and $\tau : \Theta \to \mathbb{R}$ a target function. If an estimator
$W : S \to \mathbb{R}$ is unbiased for $\tau$, then $W$ is $P_\theta$-integrable for every
$\theta \in \Theta$. -/
theorem IsUnbiased.integrable {Θ : Type*} {W : S → ℝ}
    {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ} (h : IsUnbiased W P τ)
    (θ : Θ) : Integrable W ((P θ) : Measure S) :=
  (h θ).1

/-- **An unbiased estimator has the target as its expectation.** Let $S$ be a measurable space,
$W : S \to \mathbb{R}$ an estimator, $(P_\theta)_{\theta \in \Theta}$ a family of probability
measures on $S$ and $\tau : \Theta \to \mathbb{R}$ a target function. If $W$ is unbiased for
$\tau$ under the family $(P_\theta)$, then $\int_S W \, dP_\theta = \tau(\theta)$ for every
$\theta \in \Theta$. -/
theorem IsUnbiased.expect_eq {Θ : Type*} {W : S → ℝ}
    {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ} (h : IsUnbiased W P τ)
    (θ : Θ) : ∫ x, W x ∂((P θ) : Measure S) = τ θ :=
  (h θ).2

/-- **An estimator is unbiased exactly when its bias vanishes.** Let
$(P_\theta)_{\theta \in \Theta}$ be a family of probability measures on $S$,
$\tau : \Theta \to \mathbb{R}$ a target function, and $W : S \to \mathbb{R}$ an estimator that is
$P_\theta$-integrable for every $\theta \in \Theta$. Then $W$ is unbiased for $\tau$ if and only if
its family bias $\int_S W \, dP_\theta - \tau(\theta)$ is zero for every $\theta \in \Theta$. -/
theorem isUnbiased_iff_forall_familyBias_eq_zero {Θ : Type*} {W : S → ℝ}
    {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ}
    (h : ∀ θ, Integrable W ((P θ) : Measure S)) :
    IsUnbiased W P τ ↔ ∀ θ, familyBias W P τ h θ = 0 := by
  constructor
  · intro hunb θ
    show (∫ x, W x ∂((P θ) : Measure S)) - τ θ = 0
    rw [(hunb θ).2, sub_self]
  · intro hzero θ
    refine ⟨h θ, ?_⟩
    have hz : (∫ x, W x ∂((P θ) : Measure S)) - τ θ = 0 := hzero θ
    exact sub_eq_zero.mp hz

/-- **A finite second moment makes the squared error integrable.** Let $\mu$ be a probability
measure on $S$ and $W : S \to \mathbb{R}$ an estimator in $L^2(\mu)$. Then for every
$\theta \in \mathbb{R}$ the squared error $x \mapsto (W(x) - \theta)^2$ is $\mu$-integrable. -/
theorem integrable_sq_sub_of_memLp_two {W : S → ℝ} {μ : ProbabilityMeasure S}
    {θ : ℝ} (hW : MemLp W 2 ((μ : Measure S))) :
    Integrable (fun x => (W x - θ) ^ 2) ((μ : Measure S)) := by
  have hWsub : MemLp (fun x => W x - θ) 2 ((μ : Measure S)) :=
    hW.sub (memLp_const θ)
  exact hWsub.integrable_sq

/-- **Bias–variance decomposition of the mean squared error.** Let $\mu$ be a probability measure
on a measurable space $S$, let $\theta \in \mathbb{R}$, and let $W : S \to \mathbb{R}$ be
square-integrable with respect to $\mu$, that is, $W \in L^2(\mu)$. Then the mean squared error of
$W$ at $\theta$ under $\mu$ equals $\operatorname{Var}_\mu(W) + b^2$, where
$b = \int_S W \, d\mu - \theta$ is the bias of $W$ at $\theta$ under $\mu$.

The integrability that the mean squared error and the bias require follows from $W \in L^2(\mu)$.

Source: Casella–Berger, equation (7.3.1); blueprint `af_3a1bafba0b7dff99554b01f0`. -/
theorem meanSquaredError_eq_variance_add_sq_bias {W : S → ℝ}
    {μ : ProbabilityMeasure S} {θ : ℝ} (hW : MemLp W 2 ((μ : Measure S))) :
    meanSquaredError W μ θ (integrable_sq_sub_of_memLp_two hW) =
      ProbabilityTheory.variance W ((μ : Measure S)) +
        (bias W μ θ (hW.integrable one_le_two)) ^ 2 := by
  have hW1 : Integrable W ((μ : Measure S)) := hW.integrable one_le_two
  have hWsub : MemLp (fun x => W x - θ) 2 ((μ : Measure S)) :=
    hW.sub (memLp_const θ)
  have hvar := ProbabilityTheory.variance_eq_sub (μ := ((μ : Measure S))) hWsub
  rw [ProbabilityTheory.variance_sub_const hW1.aestronglyMeasurable θ] at hvar
  have hlin : ∫ x, (W x - θ) ∂((μ : Measure S))
      = (∫ x, W x ∂((μ : Measure S))) - θ := by
    have hsub := integral_sub hW1 (integrable_const θ)
    simp only [integral_const, measureReal_def,
      IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul] at hsub
    exact hsub
  rw [hlin] at hvar
  have hsq : ∫ x, (W x - θ) ^ 2 ∂((μ : Measure S))
      = ∫ x, ((fun x => W x - θ) ^ 2) x ∂((μ : Measure S)) := by
    simp [Pi.pow_apply]
  show ∫ x, (W x - θ) ^ 2 ∂((μ : Measure S)) = _ + (_ - _) ^ 2
  rw [hsq, hvar]
  ring

/-- **Mean squared error as variance plus squared mean deviation.** Let $\mu$ be a probability
measure on a measurable space $S$, let $\theta \in \mathbb{R}$, and let $W : S \to \mathbb{R}$ be
square-integrable with respect to $\mu$, that is, $W \in L^2(\mu)$. Then the mean squared error of
$W$ at $\theta$ under $\mu$ equals
$\operatorname{Var}_\mu(W) + \left(\int_S W \, d\mu - \theta\right)^2$.

Source: Casella–Berger, equation (7.3.1) in expectation form; blueprint
`af_3a1bafba0b7dff99554b01f0`. -/
theorem meanSquaredError_eq_variance_add_sq_expectation_sub {W : S → ℝ}
    {μ : ProbabilityMeasure S} {θ : ℝ} (hW : MemLp W 2 ((μ : Measure S))) :
    meanSquaredError W μ θ (integrable_sq_sub_of_memLp_two hW) =
      ProbabilityTheory.variance W ((μ : Measure S)) +
        ((∫ x, W x ∂((μ : Measure S))) - θ) ^ 2 :=
  meanSquaredError_eq_variance_add_sq_bias hW

/-- **Bias–variance decomposition of the extended mean squared error.** Let $\mu$ be a probability
measure on a measurable space $S$, let $\theta \in \mathbb{R}$, and let $W : S \to \mathbb{R}$ be
square-integrable with respect to $\mu$, that is, $W \in L^2(\mu)$. Then the extended mean squared
error $\int_S (W(x) - \theta)^2 \, d\mu(x)$, computed in $[0, \infty]$, is finite and equals
$\operatorname{Var}_\mu(W) + b^2$, where $b = \int_S W \, d\mu - \theta$ is the bias of $W$ at
$\theta$ under $\mu$. -/
theorem ofReal_variance_add_sq_bias {W : S → ℝ} {μ : ProbabilityMeasure S}
    {θ : ℝ} (hW : MemLp W 2 ((μ : Measure S))) :
    ENNReal.ofReal (ProbabilityTheory.variance W ((μ : Measure S)) +
          (bias W μ θ (hW.integrable one_le_two)) ^ 2) =
      meanSquaredErrorENN W μ θ := by
  rw [← meanSquaredError_eq_variance_add_sq_bias hW]
  exact ofReal_meanSquaredError _

/-- **Bias–variance decomposition for a parametric family.** Let $S$ be a measurable space,
$W : S \to \mathbb{R}$ an estimator, $(P_\theta)_{\theta \in \Theta}$ a family of probability
measures on $S$ and $\tau : \Theta \to \mathbb{R}$ a target function. Suppose that for every
$\theta \in \Theta$, $W$ has a finite second moment under $P_\theta$, and $W$ and
$(W - \tau(\theta))^2$ are integrable for $P_\theta$. Then for every $\theta \in \Theta$ the family
mean squared error of $W$ at $\theta$ equals the variance $\operatorname{Var}_{P_\theta}(W)$ of
$W$ under $P_\theta$ plus the square of the family bias of $W$ at $\theta$.

Source: equation 7.3.1, in family form for a single fixed estimator. -/
theorem familyMeanSquaredError_eq_variance_add_sq_familyBias {Θ : Type*}
    {W : S → ℝ} {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ}
    (hMem : ∀ θ, MemLp W 2 (((P θ)) : Measure S))
    (h2 : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) (((P θ)) : Measure S))
    (h1 : ∀ θ, Integrable W (((P θ)) : Measure S)) (θ : Θ) :
    familyMeanSquaredError W P τ h2 θ =
      ProbabilityTheory.variance W (((P θ)) : Measure S) +
        (familyBias W P τ h1 θ) ^ 2 :=
  meanSquaredError_eq_variance_add_sq_bias (hMem θ)

/-- **Mean squared error of an unbiased estimator.** Let $\mu$ be a probability measure on a
measurable space $S$, let $\theta \in \mathbb{R}$, and let $W : S \to \mathbb{R}$ be
square-integrable with respect to $\mu$ (that is, $W \in L^2(\mu)$) and satisfy
$\int_S W \, d\mu = \theta$. Then the mean squared error of $W$ at $\theta$ under $\mu$ equals
$\operatorname{Var}_\mu(W)$.

Source: the display following Definition 7.3.2. -/
theorem meanSquaredError_eq_variance_of_expect_eq {W : S → ℝ}
    {μ : ProbabilityMeasure S} {θ : ℝ} (hW : MemLp W 2 ((μ : Measure S)))
    (hunb : ∫ x, W x ∂((μ : Measure S)) = θ) :
    meanSquaredError W μ θ (integrable_sq_sub_of_memLp_two hW) =
      ProbabilityTheory.variance W ((μ : Measure S)) := by
  have hb : bias W μ θ (hW.integrable one_le_two) = 0 := by
    show (∫ x, W x ∂((μ : Measure S))) - θ = 0
    rw [hunb, sub_self]
  rw [meanSquaredError_eq_variance_add_sq_bias hW, hb]
  simp

/-- **An unbiased estimator has mean squared error equal to its variance.** Let $S$ be a
measurable space, $W : S \to \mathbb{R}$ an estimator, $(P_\theta)_{\theta \in \Theta}$ a family of
probability measures on $S$ and $\tau : \Theta \to \mathbb{R}$ a target function. Suppose that $W$
is unbiased for $\tau$ under the family, and that for every $\theta \in \Theta$, $W$ has a finite
second moment under $P_\theta$ and $(W - \tau(\theta))^2$ is integrable for $P_\theta$. Then for
every $\theta \in \Theta$ the family mean squared error of $W$ at $\theta$ equals the variance
$\operatorname{Var}_{P_\theta}(W)$ of $W$ under $P_\theta$. -/
theorem IsUnbiased.familyMeanSquaredError_eq_variance {Θ : Type*} {W : S → ℝ}
    {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ} (hunb : IsUnbiased W P τ)
    (hMem : ∀ θ, MemLp W 2 (((P θ)) : Measure S))
    (h2 : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) (((P θ)) : Measure S))
    (θ : Θ) :
    familyMeanSquaredError W P τ h2 θ =
      ProbabilityTheory.variance W (((P θ)) : Measure S) := by
  have h := familyMeanSquaredError_eq_variance_add_sq_familyBias hMem h2
    (fun θ => (hMem θ).integrable one_le_two) θ
  have hb : familyBias W P τ (fun θ => (hMem θ).integrable one_le_two) θ
      = 0 := by
    show (∫ x, W x ∂(((P θ)) : Measure S)) - τ θ = 0
    rw [hunb.expect_eq θ, sub_self]
  rw [h, hb]
  simp

/-- **Frequentist risk.** Let $S$ be a measurable space, $\delta : S \to A$ a decision rule,
$(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$, and
$\ell : \Theta \times A \to [0, \infty)$ a loss such that $x \mapsto \ell(\theta, \delta(x))$ is
$P_\theta$-integrable for every $\theta \in \Theta$. The frequentist risk of $\delta$ is the
function $\Theta \to \mathbb{R}$ given by
$R(\theta, \delta) = \int_S \ell(\theta, \delta(x)) \, dP_\theta(x)$.

The rule $\delta$ does not depend on $\theta$, and the action space $A$ may differ from $\Theta$.
No prior, kernel or optimality criterion enters.

Source: Casella–Berger equation 7.3.16; the integrability hypothesis is the expectation domain of
Chapter 2 Definition 2.2.1. Blueprint `af_36871388da7326a07a5e4f71`. -/
noncomputable def frequentistRisk {Θ A : Type*} (δ : S → A)
    (P : Θ → ProbabilityMeasure S) (ℓ : Θ → A → NNReal)
    (_h : ∀ θ, Integrable (fun x => (ℓ θ (δ x) : ℝ)) ((P θ) : Measure S)) :
    Θ → ℝ :=
  fun θ => ∫ x, (ℓ θ (δ x) : ℝ) ∂((P θ) : Measure S)

/-- **Frequentist risk as an integral.** Let $S$ be a measurable space, $\delta : S \to A$ a
decision rule, $(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$ and
$\ell : \Theta \times A \to [0, \infty)$ a loss function such that
$x \mapsto \ell(\theta, \delta(x))$ is integrable for $P_\theta$ for every $\theta \in \Theta$.
Then for every $\theta \in \Theta$ the frequentist risk of $\delta$ at $\theta$ equals
$\int_S \ell(\theta, \delta(x)) \, dP_\theta(x)$. -/
theorem frequentistRisk_apply {Θ A : Type*} {δ : S → A}
    {P : Θ → ProbabilityMeasure S} {ℓ : Θ → A → NNReal}
    {h : ∀ θ, Integrable (fun x => (ℓ θ (δ x) : ℝ)) ((P θ) : Measure S)}
    (θ : Θ) :
    frequentistRisk δ P ℓ h θ =
      ∫ x, (ℓ θ (δ x) : ℝ) ∂((P θ) : Measure S) :=
  rfl

/-- **Frequentist risk is nonnegative.** Let $\delta : S \to A$ be a decision rule,
$(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$, and
$\ell : \Theta \times A \to [0, \infty)$ a loss such that $x \mapsto \ell(\theta, \delta(x))$ is
$P_\theta$-integrable for every $\theta \in \Theta$. Then the frequentist risk $R(\theta, \delta)$
of $\delta$ at $\theta$ is nonnegative for every $\theta \in \Theta$. -/
theorem frequentistRisk_nonneg {Θ A : Type*} {δ : S → A}
    {P : Θ → ProbabilityMeasure S} {ℓ : Θ → A → NNReal}
    {h : ∀ θ, Integrable (fun x => (ℓ θ (δ x) : ℝ)) ((P θ) : Measure S)}
    (θ : Θ) : 0 ≤ frequentistRisk δ P ℓ h θ := by
  unfold frequentistRisk
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => NNReal.coe_nonneg _)

/-- **Extended frequentist risk.** Let $S$ be a measurable space, $\delta : S \to A$ a decision
rule, $(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$, and
$\ell : \Theta \times A \to [0, \infty)$ a loss. The extended frequentist risk of $\delta$ at
$\theta \in \Theta$ is the Lebesgue integral $\int_S \ell(\theta, \delta(x)) \, dP_\theta(x)$, taken
in $[0, \infty]$.

When the loss is $P_\theta$-integrable for every $\theta$, this is the frequentist risk; when it is
measurable but not integrable at $\theta$, it equals $\infty$.

Source: blueprint `af_36871388da7326a07a5e4f71`. -/
noncomputable def frequentistRiskENN {Θ A : Type*} (δ : S → A)
    (P : Θ → ProbabilityMeasure S) (ℓ : Θ → A → NNReal) (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ x, ℓ θ (δ x) ∂((P θ) : Measure S)

/-- **Finite and extended frequentist risk agree.** Let $\Theta$ and $A$ be sets, let
$(P_\vartheta)_{\vartheta \in \Theta}$ be a family of probability measures on a measurable space
$S$, let $\delta : S \to A$ be a decision rule and $\ell : \Theta \times A \to [0, \infty)$ a
loss, and suppose $x \mapsto \ell(\vartheta, \delta(x))$ is $P_\vartheta$-integrable for every
$\vartheta \in \Theta$. Then for every $\theta \in \Theta$ the extended frequentist risk
$\int_S \ell(\theta, \delta(x)) \, dP_\theta(x)$, computed in $[0, \infty]$, is finite and equals
the frequentist risk of $\delta$ at $\theta$.

Source: blueprint `af_36871388da7326a07a5e4f71`. -/
theorem ofReal_frequentistRisk {Θ A : Type*} {δ : S → A}
    {P : Θ → ProbabilityMeasure S} {ℓ : Θ → A → NNReal}
    {h : ∀ θ, Integrable (fun x => (ℓ θ (δ x) : ℝ)) ((P θ) : Measure S)}
    (θ : Θ) :
    ENNReal.ofReal (frequentistRisk δ P ℓ h θ) =
      frequentistRiskENN δ P ℓ θ := by
  unfold frequentistRisk frequentistRiskENN
  exact (lintegral_coe_eq_integral (fun x => ℓ θ (δ x)) (h θ)).symm

/-- **Extended frequentist risk of a measurable non-integrable loss is infinite.** Let $S$ be a
measurable space, $\delta : S \to A$ a decision rule, $(P_\theta)_{\theta \in \Theta}$ a family of
probability measures on $S$, $\ell : \Theta \times A \to [0, \infty)$ a loss, and
$\theta \in \Theta$. If the function $x \mapsto \ell(\theta, \delta(x))$ is almost everywhere
strongly measurable with respect to $P_\theta$ but not $P_\theta$-integrable, then the extended
frequentist risk $\int_S \ell(\theta, \delta(x)) \, dP_\theta(x) \in [0, \infty]$ of $\delta$ at
$\theta$ equals $\infty$.

So a measurable non-integrable loss is never assigned a finite extended risk.

Source: blueprint `af_36871388da7326a07a5e4f71`. -/
theorem frequentistRiskENN_eq_top_of_not_integrable {Θ A : Type*}
    {δ : S → A} {P : Θ → ProbabilityMeasure S} {ℓ : Θ → A → NNReal}
    {θ : Θ}
    (hm : AEStronglyMeasurable (fun x => (ℓ θ (δ x) : ℝ))
      ((P θ) : Measure S))
    (h : ¬ Integrable (fun x => (ℓ θ (δ x) : ℝ)) ((P θ) : Measure S)) :
    frequentistRiskENN δ P ℓ θ = ∞ := by
  have hnn : 0 ≤ᵐ[((P θ) : Measure S)] (fun x => (ℓ θ (δ x) : ℝ)) :=
    Filter.Eventually.of_forall fun x => NNReal.coe_nonneg _
  have hiff := lintegral_ofReal_ne_top_iff_integrable hm hnn
  have htop : ∫⁻ x, ENNReal.ofReal ((ℓ θ (δ x) : ℝ)) ∂((P θ) : Measure S)
      = ∞ := by
    by_contra hne
    exact h (hiff.mp hne)
  unfold frequentistRiskENN
  calc ∫⁻ x, (ℓ θ (δ x) : ℝ≥0∞) ∂((P θ) : Measure S)
        = ∫⁻ x, ENNReal.ofReal ((ℓ θ (δ x) : ℝ)) ∂((P θ) : Measure S) := by
          refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact ENNReal.ofReal_coe_nnreal.symm
      _ = ∞ := htop

/-- **Mean squared error is frequentist risk under squared-error loss.** Let
$(P_\theta)_{\theta \in \Theta}$ be a family of probability measures on $S$,
$W : S \to \mathbb{R}$ an estimator and $\tau : \Theta \to \mathbb{R}$ a target function such that
$x \mapsto (W(x) - \tau(\theta))^2$ is $P_\theta$-integrable for every $\theta \in \Theta$. Then for
every $\theta$, the frequentist risk at $\theta$ of $W$, as a decision rule with actions in
$\mathbb{R}$, under the squared-error loss $\ell(\theta, a) = (a - \tau(\theta))^2$ equals the
family mean squared error of $W$ for $\tau$ at $\theta$.

Source: blueprint `af_36871388da7326a07a5e4f71`. -/
theorem frequentistRisk_squared_eq_familyMeanSquaredError {Θ : Type*}
    {W : S → ℝ} {P : Θ → ProbabilityMeasure S} {τ : Θ → ℝ}
    (hRisk : ∀ θ, Integrable
      (fun x => ((⟨(W x - τ θ) ^ 2, sq_nonneg _⟩ : NNReal) : ℝ))
      (((P θ)) : Measure S))
    (hMSE : ∀ θ, Integrable (fun x => (W x - τ θ) ^ 2) (((P θ)) : Measure S)) :
    frequentistRisk W P (fun θ a => ⟨(a - τ θ) ^ 2, sq_nonneg _⟩) hRisk =
      familyMeanSquaredError W P τ hMSE :=
  rfl

end

end MathlibExt.Probability.Statistics.EstimationRisk
