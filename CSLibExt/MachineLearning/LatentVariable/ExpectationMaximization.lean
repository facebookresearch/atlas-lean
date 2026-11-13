/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import MathlibExt.InformationTheory.LogSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Expectation-maximization never decreases the likelihood

The expectation-maximization algorithm (Dempster, Laird and Rubin, *Maximum likelihood from
incomplete data via the EM algorithm*, J. Roy. Statist. Soc. B 39, 1977; Bishop, *Pattern
Recognition and Machine Learning*, Section 9.4) for a model `p θ x z > 0` with a finite latent
space `Z` and data `xs : Fin N → X`. The log-likelihood is `logLik θ = ∑ n, log ∑ z, p θ (xs n) z`;
the E-step computes the posteriors `posterior θ x z = p θ x z / ∑ z', p θ x z'`; the M-step
increases `emQ θ' θ = ∑ n, ∑ z, posterior θ (xs n) z * log (p θ' (xs n) z)` in `θ'`.

Main results:

* `sum_mul_log_sub_le`: Gibbs' inequality `∑ q (log p - log q) ≤ log ∑ p` for a distribution `q`
  (from MathlibExt's log-sum inequality, `MathlibExt/InformationTheory/LogSum.lean`), tight at
  `q = p / ∑ p` (`sum_div_mul_log_sub`).
* `elbo_le_logLik`: **the evidence lower bound** `elbo θ q ≤ logLik θ` for all latent
  distributions; `elbo_posterior`: **equality at the posterior**.
* `emQ_sub_le_logLik_sub`: `ℓ(θ') - ℓ(θ) ≥ Q(θ' | θ) - Q(θ | θ)`; `logLik_le_of_emQ_le`: **the EM
  theorem**, a step that does not decrease `Q(· | θ)` does not decrease the likelihood.
* `logLik_iterate_monotone`: **the likelihood is monotone along the EM iterates** of any M-step
  with `Q(M θ | θ) ≥ Q(θ | θ)`.

## Relation to `FormalizedTextbooks`

`FormalizedTextbooks/UnderstandingMachineLearningFromTheoryToAlgorithms/Ch24.lean` states the
monotonicity of EM as a hypothesis (`EMMonotone L : ∀ t, L t ≤ L (t + 1)` on a bare sequence `L`);
`logLik_iterate_monotone` proves it for the log-likelihood along EM iterates. The two-component
symmetric Gaussian mixture of
`FormalizedTextbooks/HighDimensionalProbability/Chapter04/Section07/GaussianMixtureModel.lean` is a
distributional statement and does not involve EM.

## Cost model

No running-time model: the subject is the likelihood, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LatentVariable.ExpectationMaximization

open Real

variable {Θ X Z : Type*} [Fintype Z]

/-! ## Gibbs' inequality -/

/-- **Probability distributions on a finite latent space.** A function $q : Z \to \mathbb{R}$ on a
finite set $Z$ is a probability distribution when $q(z) \ge 0$ for every $z \in Z$ and
$\sum_{z \in Z} q(z) = 1$. -/
def IsDist (q : Z → ℝ) : Prop := (∀ z, 0 ≤ q z) ∧ ∑ z, q z = 1

/-- **Gibbs' inequality (evidence lower bound form).** Let $Z$ be a finite set, let
$p : Z \to \mathbb{R}$ satisfy $p(z) > 0$ for all $z$, and let $q$ be a probability distribution
on $Z$. Then $\sum_{z \in Z} q(z) (\log p(z) - \log q(z)) \le \log \sum_{z \in Z} p(z)$.

This is the log-sum inequality with $\sum_{z} q(z) = 1$; terms with $q(z) = 0$ contribute $0$. -/
theorem sum_mul_log_sub_le {p q : Z → ℝ} (hp : ∀ z, 0 < p z) (hq : IsDist q) :
    ∑ z, q z * (log (p z) - log (q z)) ≤ log (∑ z, p z) := by
  obtain ⟨hq0, hq1⟩ := hq
  have h := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div Finset.univ q p
    (fun z _ => hq0 z) (fun z _ => hp z)
  rw [hq1, one_mul, one_div, log_inv] at h
  have hterm : ∀ z, q z * log (q z / p z) = -(q z * (log (p z) - log (q z))) := by
    intro z
    rcases (hq0 z).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [log_div hpos.ne' (hp z).ne']; ring
  simp only [hterm, Finset.sum_neg_distrib] at h
  linarith

/-- **Equality case of Gibbs' inequality.** Let $Z$ be a finite nonempty set, let
$p : Z \to \mathbb{R}$ satisfy $p(z) > 0$ for all $z$, and write $P = \sum_{z \in Z} p(z)$. Then

$$\sum_{z \in Z} \frac{p(z)}{P} \left(\log p(z) - \log \frac{p(z)}{P}\right) = \log P,$$

that is, the bound of Gibbs' inequality is attained at the distribution $q = p / P$. -/
theorem sum_div_mul_log_sub {p : Z → ℝ} (hp : ∀ z, 0 < p z) [Nonempty Z] :
    ∑ z, p z / (∑ z', p z') * (log (p z) - log (p z / ∑ z', p z')) = log (∑ z, p z) := by
  have hPpos : 0 < ∑ z', p z' := Finset.sum_pos (fun z _ => hp z) Finset.univ_nonempty
  have : ∀ z, p z / (∑ z', p z') * (log (p z) - log (p z / ∑ z', p z')) =
      p z / (∑ z', p z') * log (∑ z', p z') := by
    intro z
    rw [log_div (hp z).ne' hPpos.ne']
    ring
  rw [Finset.sum_congr rfl fun z _ => this z, ← Finset.sum_mul, ← Finset.sum_div,
    div_self hPpos.ne', one_mul]

/-! ## The model -/

variable {N : ℕ}

/-- **Marginal of a latent-variable model.** For a joint model $p$ assigning a real number
$p_\theta(x, z)$ to each parameter $\theta$, observation $x$ and latent value $z$ in a finite
latent space $Z$, the marginal is $p_\theta(x) = \sum_{z \in Z} p_\theta(x, z)$. -/
def marginal (p : Θ → X → Z → ℝ) (θ : Θ) (x : X) : ℝ := ∑ z, p θ x z

/-- **Log-likelihood of a latent-variable model.** For a joint model $p$ with finite latent space
$Z$ and data $x_0, \dots, x_{N-1}$, the log-likelihood at the parameter $\theta$ is
$\ell(\theta) = \sum_{n < N} \log p_\theta(x_n)$, where
$p_\theta(x) = \sum_{z \in Z} p_\theta(x, z)$ is the marginal. -/
noncomputable def logLik (p : Θ → X → Z → ℝ) (xs : Fin N → X) (θ : Θ) : ℝ :=
  ∑ n, log (marginal p θ (xs n))

/-- **Posterior of a latent-variable model.** For a joint model $p$ with finite latent space $Z$,
the posterior of the latent value $z$ given the observation $x$ at the parameter $\theta$ is
$p_\theta(z \mid x) = p_\theta(x, z) / p_\theta(x)$, where
$p_\theta(x) = \sum_{z' \in Z} p_\theta(x, z')$ is the marginal (the quotient is read as $0$
when the marginal is $0$). Computing it is the E-step of expectation-maximization. -/
noncomputable def posterior (p : Θ → X → Z → ℝ) (θ : Θ) (x : X) (z : Z) : ℝ :=
  p θ x z / marginal p θ x

/-- **Evidence lower bound of latent distributions.** Let $Z$ be a finite set, let
$p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values
$z \in Z$, and let $x_1, \dots, x_N$ be data. For a parameter $\theta$ and functions
$q_1, \dots, q_N : Z \to \mathbb{R}$ (one latent distribution per data point), the evidence lower
bound is $\sum_{n=1}^N \sum_{z \in Z} q_n(z) \bigl(\log p_\theta(x_n, z) - \log q_n(z)\bigr)$. -/
noncomputable def elbo (p : Θ → X → Z → ℝ) (xs : Fin N → X) (θ : Θ) (q : Fin N → Z → ℝ) : ℝ :=
  ∑ n, ∑ z, q n z * (log (p θ (xs n) z) - log (q n z))

/-- **The EM objective.** Let $Z$ be a finite set, let $p_\theta(x, z)$ be real numbers indexed by
parameters $\theta$, observations $x$ and latent values $z \in Z$, let $x_1, \dots, x_N$ be data,
and write $p_\theta(z \mid x) = p_\theta(x, z) / \sum_{z' \in Z} p_\theta(x, z')$ for the posterior.
For parameters $\theta'$ and $\theta$, the EM objective is
$Q(\theta' \mid \theta) = \sum_{n=1}^N \sum_{z \in Z} p_\theta(z \mid x_n) \log p_{\theta'}(x_n, z)$
(maximized over $\theta'$ in the M-step). -/
noncomputable def emQ (p : Θ → X → Z → ℝ) (xs : Fin N → X) (θ' θ : Θ) : ℝ :=
  ∑ n, ∑ z, posterior p θ (xs n) z * log (p θ' (xs n) z)

/-- **Posterior entropy.** For a joint model $p$ with finite latent space $Z$, data
$x_0, \dots, x_{N-1}$ and a parameter $\theta$, the posterior entropy is
$-\sum_{n < N} \sum_{z \in Z} p_\theta(z \mid x_n) \log p_\theta(z \mid x_n)$, where
$p_\theta(z \mid x)$ is the posterior of $z$ given $x$. -/
noncomputable def postEntropy (p : Θ → X → Z → ℝ) (xs : Fin N → X) (θ : Θ) : ℝ :=
  -∑ n, ∑ z, posterior p θ (xs n) z * log (posterior p θ (xs n) z)

variable {p : Θ → X → Z → ℝ}

/-- **Posteriors are probability distributions.** Let $Z$ be a nonempty finite set and let
$p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values
$z \in Z$, with $p_\theta(x, z) > 0$ for all $\theta$, $x$, $z$. For every parameter $\theta$ and
observation $x$, the posterior $z \mapsto p_\theta(x, z) / \sum_{z' \in Z} p_\theta(x, z')$ is a
probability distribution on $Z$: its values are nonnegative and sum to $1$. -/
theorem isDist_posterior [Nonempty Z] (hp : ∀ θ x z, 0 < p θ x z) (θ : Θ) (x : X) :
    IsDist (posterior p θ x) := by
  have hpos : 0 < marginal p θ x := Finset.sum_pos (fun z _ => hp θ x z) Finset.univ_nonempty
  refine ⟨fun z => (div_pos (hp θ x z) hpos).le, ?_⟩
  simp only [posterior]
  rw [← Finset.sum_div]
  exact div_self hpos.ne'

/-- **The evidence lower bound.** Let $Z$ be a finite set, let $p_\theta(x, z)$ be real numbers
indexed by parameters $\theta$, observations $x$ and latent values $z \in Z$, with
$p_\theta(x, z) > 0$ for all $\theta$, $x$, $z$, and let $x_1, \dots, x_N$ be data. For every
parameter $\theta$ and all probability distributions $q_1, \dots, q_N$ on $Z$,
$$
\sum_{n=1}^N \sum_{z \in Z} q_n(z) \bigl(\log p_\theta(x_n, z) - \log q_n(z)\bigr) \le
\sum_{n=1}^N \log \sum_{z \in Z} p_\theta(x_n, z),
$$
that is, the evidence lower bound of $q_1, \dots, q_N$ at $\theta$ is at most the log-likelihood
of the data at $\theta$. Terms with $q_n(z) = 0$ count as $0$. -/
theorem elbo_le_logLik (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X) (θ : Θ)
    {q : Fin N → Z → ℝ} (hq : ∀ n, IsDist (q n)) : elbo p xs θ q ≤ logLik p xs θ :=
  Finset.sum_le_sum fun n _ => sum_mul_log_sub_le (fun z => hp θ (xs n) z) (hq n)

/-- **The bound is tight at the posterior.** Let $Z$ be a nonempty finite set, let
$p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values
$z \in Z$, with $p_\theta(x, z) > 0$ for all $\theta$, $x$, $z$, and let $x_1, \dots, x_N$ be data.
For every parameter $\theta$, the posteriors
$q_n(z) = p_\theta(z \mid x_n) = p_\theta(x_n, z) / \sum_{z' \in Z} p_\theta(x_n, z')$ satisfy
$$
\sum_{n=1}^N \sum_{z \in Z} q_n(z) \bigl(\log p_\theta(x_n, z) - \log q_n(z)\bigr) =
\sum_{n=1}^N \log \sum_{z \in Z} p_\theta(x_n, z),
$$
that is, the evidence lower bound at $\theta$ of the posteriors equals the log-likelihood of the
data at $\theta$. -/
theorem elbo_posterior [Nonempty Z] (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X) (θ : Θ) :
    elbo p xs θ (fun n => posterior p θ (xs n)) = logLik p xs θ :=
  Finset.sum_congr rfl fun n _ => sum_div_mul_log_sub fun z => hp θ (xs n) z

/-- **The ELBO at the posterior is the EM objective plus the entropy.** Let $Z$ be a finite set,
let $p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent
values $z \in Z$, let $x_1, \dots, x_N$ be data, and write
$p_\theta(z \mid x) = p_\theta(x, z) / \sum_{z' \in Z} p_\theta(x, z')$ for the posterior,
$Q(\theta' \mid \theta) = \sum_{n=1}^N \sum_{z \in Z} p_\theta(z \mid x_n) \log p_{\theta'}(x_n, z)$
for the EM objective and
$H(\theta) = -\sum_{n=1}^N \sum_{z \in Z} p_\theta(z \mid x_n) \log p_\theta(z \mid x_n)$ for the
entropy of the posteriors. For all parameters $\theta'$ and $\theta$, the evidence lower bound at
$\theta'$ of the posteriors $q_n = p_\theta(\cdot \mid x_n)$ satisfies
$$
\sum_{n=1}^N \sum_{z \in Z} q_n(z) \bigl(\log p_{\theta'}(x_n, z) - \log q_n(z)\bigr) =
Q(\theta' \mid \theta) + H(\theta),
$$
that is, it splits as the EM objective $Q(\theta' \mid \theta)$ plus the posterior entropy. -/
theorem elbo_posterior_eq (xs : Fin N → X) (θ' θ : Θ) :
    elbo p xs θ' (fun n => posterior p θ (xs n)) = emQ p xs θ' θ + postEntropy p xs θ := by
  simp only [elbo, emQ, postEntropy, mul_sub, Finset.sum_sub_distrib]
  ring

/-- **The EM inequality.** Let $Z$ be a nonempty finite set, let $p_\theta(x, z)$ be real numbers
indexed by parameters $\theta$, observations $x$ and latent values $z \in Z$, with
$p_\theta(x, z) > 0$ for all $\theta$, $x$, $z$, and let $x_1, \dots, x_N$ be data. Write
$p_\theta(z \mid x) = p_\theta(x, z) / \sum_{z' \in Z} p_\theta(x, z')$ for the posterior,
$Q(\theta' \mid \theta) = \sum_{n=1}^N \sum_{z \in Z} p_\theta(z \mid x_n) \log p_{\theta'}(x_n, z)$
for the EM objective and $\ell(\theta) = \sum_{n=1}^N \log \sum_{z \in Z} p_\theta(x_n, z)$ for the
log-likelihood. For all parameters $\theta'$ and $\theta$,
$Q(\theta' \mid \theta) - Q(\theta \mid \theta) \le \ell(\theta') - \ell(\theta)$: the
log-likelihood gains at least as much as $Q(\cdot \mid \theta)$. -/
theorem emQ_sub_le_logLik_sub [Nonempty Z] (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X)
    (θ' θ : Θ) : emQ p xs θ' θ - emQ p xs θ θ ≤ logLik p xs θ' - logLik p xs θ := by
  have h1 := elbo_le_logLik hp xs θ' (q := fun n => posterior p θ (xs n))
    fun n => isDist_posterior hp θ (xs n)
  have h2 := elbo_posterior hp xs θ
  rw [elbo_posterior_eq] at h1 h2
  linarith

/-- **The EM theorem.** Let $Z$ be a nonempty finite set, let $p_\theta(x, z)$ be real numbers
indexed by parameters $\theta$, observations $x$ and latent values $z \in Z$, with
$p_\theta(x, z) > 0$ for all $\theta$, $x$, $z$, and let $x_1, \dots, x_N$ be data. Write
$p_\theta(z \mid x) = p_\theta(x, z) / \sum_{z' \in Z} p_\theta(x, z')$ for the posterior,
$Q(\theta' \mid \theta) = \sum_{n=1}^N \sum_{z \in Z} p_\theta(z \mid x_n) \log p_{\theta'}(x_n, z)$
for the EM objective and $\ell(\theta) = \sum_{n=1}^N \log \sum_{z \in Z} p_\theta(x_n, z)$ for the
log-likelihood. For parameters $\theta$ and $\theta'$, if
$Q(\theta \mid \theta) \le Q(\theta' \mid \theta)$, then $\ell(\theta) \le \ell(\theta')$: a step
that does not decrease $Q(\cdot \mid \theta)$ does not decrease the log-likelihood. -/
theorem logLik_le_of_emQ_le [Nonempty Z] (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X)
    {θ' θ : Θ} (h : emQ p xs θ θ ≤ emQ p xs θ' θ) : logLik p xs θ ≤ logLik p xs θ' := by
  have := emQ_sub_le_logLik_sub hp xs θ' θ
  linarith

/-- **EM iterates have monotone likelihood.** Let $Z$ be a nonempty finite set, let
$p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values
$z \in Z$, with $p_\theta(x, z) > 0$ for all $\theta$, $x$, $z$, and let $x_1, \dots, x_N$ be data.
Write $p_\theta(z \mid x) = p_\theta(x, z) / \sum_{z' \in Z} p_\theta(x, z')$ for the posterior,
$Q(\theta' \mid \theta) = \sum_{n=1}^N \sum_{z \in Z} p_\theta(z \mid x_n) \log p_{\theta'}(x_n, z)$
for the EM objective and $\ell(\theta) = \sum_{n=1}^N \log \sum_{z \in Z} p_\theta(x_n, z)$ for the
log-likelihood. Let $M$ be a map on parameters, with $k$-th iterate $M^k$ ($M^0$ the identity),
such that $Q(M\theta \mid \theta) \ge Q(\theta \mid \theta)$ for every $\theta$ (in particular if
$M\theta$ maximizes $Q(\cdot \mid \theta)$, or $M$ is a generalized-EM step). Then for every
$\theta_0$ the sequence $k \mapsto \ell(M^k \theta_0)$ is nondecreasing. -/
theorem logLik_iterate_monotone [Nonempty Z] (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X)
    {M : Θ → Θ} (hM : ∀ θ, emQ p xs θ θ ≤ emQ p xs (M θ) θ) (θ₀ : Θ) :
    Monotone fun k => logLik p xs (M^[k] θ₀) := by
  refine monotone_nat_of_le_succ fun k => ?_
  simp only [Function.iterate_succ_apply']
  exact logLik_le_of_emQ_le hp xs (hM _)

end Cslib.MachineLearning.LatentVariable.ExpectationMaximization
