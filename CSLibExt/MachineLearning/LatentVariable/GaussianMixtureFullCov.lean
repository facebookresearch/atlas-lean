/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ExpectationMaximization
public import MathlibExt.Probability.Distributions.GaussianMLE

/-!
# EM for Gaussian mixtures with full covariances

The EM algorithm for a mixture of `K` Gaussians with full covariance matrices in
`EuclideanSpace ℝ (Fin d)` (Bishop, *Pattern Recognition and Machine Learning*, Section 9.2.2), as
an instance of the generic EM of `LatentVariable/ExpectationMaximization.lean`. The component
density is the multivariate Gaussian density `MetaMathlibExt.multivariateGaussianPDFReal`, proved
in MathlibExt to be the density of Mathlib's `multivariateGaussian`.

Main results:

* `joint` (`π k N(x | μ k, Σ k)`) on `ValidParams` (positive weights summing to one, positive
  definite covariances); `resp`, the E-step responsibilities, is the posterior `P(z = k | xₙ)`.
* The M-step `mStep`: `π k' = N k / N` (`mass`), `μ k'` the responsibility-weighted mean
  (`newMean`), and **`Σ k'` the responsibility-weighted sample covariance** (`newCov`), with
  MathlibExt's `weightedMean` and `weightedScatter`. On data in general position
  (`SpansAffinely`: not all in an affine hyperplane) the covariance update is positive definite
  (`newCov_posDef`), so the M-step is valid (`mStep_valid`, `emStep`).
* `compTerm_le`: **the mean and covariance updates maximize each component term of `Q`** over all
  means and positive definite covariances: the weighted Gaussian MLE
  `MetaMathlibExt.sum_mul_log_multivariateGaussianPDFReal_le` with the responsibilities as
  weights.
* `emQ_le_emStep`: the M-step maximizes `Q(· | θ)` over all valid parameters;
  `logLik_le_emStep`, `logLik_iterate_emStep_monotone`: **each EM step does not decrease the
  log-likelihood**, and the log-likelihood is monotone along the EM iterates.

`LatentVariable/GaussianMixture.lean` treats the isotropic case `Σ k = σ k² I`.

## Cost model

No running-time model: the subject is the likelihood, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LatentVariable.GaussianMixtureFullCov

open Real Matrix WithLp MetaMathlibExt
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open scoped RealInnerProductSpace

variable {d K N : ℕ}

/-! ## The model -/

/-- **Parameters of a full-covariance Gaussian mixture.** A parameter of the $K$-component
Gaussian mixture in $d$ dimensions with full covariances consists of, for each component
$k < K$, a real mixing weight $\pi_k$, a mean $\mu_k \in \mathbb{R}^d$ and a real $d \times d$
covariance matrix $\Sigma_k$, with no constraints imposed. -/
structure Params (d K : ℕ) where
  /-- The mixing weights `π k`. -/
  weight : Fin K → ℝ
  /-- The component means `μ k`. -/
  mean : Fin K → EuclideanSpace ℝ (Fin d)
  /-- The component covariances `Σ k`. -/
  cov : Fin K → Matrix (Fin d) (Fin d) ℝ

/-- **Validity of full-covariance Gaussian mixture parameters.** Parameters
$(\pi_k, \mu_k, \Sigma_k)_{k<K}$ of a $K$-component Gaussian mixture in $d$ dimensions are valid
when every weight $\pi_k$ is positive, the weights sum to one, and every covariance matrix
$\Sigma_k$ is positive definite. -/
structure Params.Valid (θ : Params d K) : Prop where
  weight_pos : ∀ k, 0 < θ.weight k
  weight_sum : ∑ k, θ.weight k = 1
  cov_posDef : ∀ k, (θ.cov k).PosDef

/-- **Valid parameters of a full-covariance Gaussian mixture.** The parameter space of EM for the
$K$-component Gaussian mixture in $d$ dimensions with full covariances is the set of parameters
$(\pi_k, \mu_k, \Sigma_k)_{k<K}$ that are valid: every weight $\pi_k$ is positive, the weights
sum to one, and every covariance matrix $\Sigma_k$ is positive definite. -/
abbrev ValidParams (d K : ℕ) := {θ : Params d K // θ.Valid}

/-- **Joint density of the full-covariance Gaussian mixture.** For valid parameters $\theta$ with
weights $\pi_k$, means $\mu_k$ and covariances $\Sigma_k$, the joint density of a point
$x \in \mathbb{R}^d$ and a component $k$ is
$p_\theta(x, k) = \pi_k \, \mathcal{N}(x \mid \mu_k, \Sigma_k)$, where
$\mathcal{N}(x \mid \mu, \Sigma)$ is the multivariate Gaussian density. -/
noncomputable def joint (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) : ℝ :=
  θ.1.weight k * multivariateGaussianPDFReal (θ.1.mean k) (θ.1.cov k) x

theorem joint_pos (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) :
    0 < joint θ x k :=
  mul_pos (θ.2.weight_pos k) (multivariateGaussianPDFReal_pos _ (θ.2.cov_posDef k) x)

/-- **Responsibilities of the full-covariance Gaussian mixture.** For valid parameters
$\theta = (\pi_j, \mu_j, \Sigma_j)_{j<K}$, a point $x \in \mathbb{R}^d$ and a component $k$, write
$p_k(x) = \pi_k \, \mathcal{N}(x \mid \mu_k, \Sigma_k)$, where $\mathcal{N}(\cdot \mid \mu, \Sigma)$
is the multivariate Gaussian density. The responsibility of $k$ for $x$ is the posterior
probability of component $k$ given $x$ (the E-step),
$$r_k(x) = \frac{p_k(x)}{\sum_j p_j(x)}.$$
For data $(x_n)_{n<N}$ one writes $r_{nk} = r_k(x_n)$. -/
noncomputable def resp (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) : ℝ :=
  posterior joint θ x k

theorem resp_pos (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) :
    0 < resp θ x k :=
  div_pos (joint_pos θ x k) (Finset.sum_pos (fun k _ => joint_pos θ x k) ⟨k, Finset.mem_univ k⟩)

theorem nonempty_of_valid (θ : ValidParams d K) : Nonempty (Fin K) := by
  by_contra h
  have : IsEmpty (Fin K) := not_nonempty_iff.1 h
  have := θ.2.weight_sum
  simp at this

theorem sum_resp (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) : ∑ k, resp θ x k = 1 := by
  have := nonempty_of_valid θ
  exact (isDist_posterior (fun θ x k => joint_pos θ x k) θ x).2

/-! ## The M-step -/

variable (xs : Fin N → EuclideanSpace ℝ (Fin d))

/-- **Effective number of points of a full-covariance mixture component.** For data
$x_1, \dots, x_N \in \mathbb{R}^d$ and valid parameters $\theta$ with responsibilities $r_{nk}$,
the effective number of points of component $k$ is $N_k = \sum_n r_{nk}$. -/
noncomputable def mass (θ : ValidParams d K) (k : Fin K) : ℝ := ∑ n, resp θ (xs n) k

/-- **Mean update of the full-covariance Gaussian mixture.** Given data $(x_n)_{n<N}$ in
$\mathbb{R}^d$, valid parameters $\theta$ and a component $k$, let $r_{nk}$ be the
responsibility of component $k$ for $x_n$ and let $N_k = \sum_n r_{nk}$. The mean update is the
responsibility-weighted mean
$$\mu_k' = \frac{1}{N_k} \sum_n r_{nk} x_n \in \mathbb{R}^d.$$

When there are no data ($N = 0$), $N_k = 0$ and the convention $N_k^{-1} = 0$ makes
$\mu_k' = 0$. -/
noncomputable def newMean (θ : ValidParams d K) (k : Fin K) : EuclideanSpace ℝ (Fin d) :=
  weightedMean (fun n => resp θ (xs n) k) xs

/-- **Covariance update of the full-covariance Gaussian mixture.** Given data $(x_n)_{n<N}$
in $\mathbb{R}^d$, valid parameters $\theta$ and a component $k$, let $r_{nk}$ be the
responsibility of component $k$ for $x_n$, let $N_k = \sum_n r_{nk}$, and let $\mu_k'$ be the
responsibility-weighted mean $N_k^{-1} \sum_n r_{nk} x_n$. The covariance update is the real
$d \times d$ matrix
$$\Sigma_k' = \frac{1}{N_k} \sum_n r_{nk} (x_n - \mu_k')(x_n - \mu_k')^{\top}.$$

When there are no data ($N = 0$), $N_k = 0$ and the convention $N_k^{-1} = 0$ makes
$\Sigma_k' = 0$. -/
noncomputable def newCov (θ : ValidParams d K) (k : Fin K) : Matrix (Fin d) (Fin d) ℝ :=
  weightedScatter (fun n => resp θ (xs n) k) xs (newMean xs θ k)

/-- **M-step of the full-covariance Gaussian mixture.** For data
$x_1, \dots, x_N \in \mathbb{R}^d$ and valid parameters $\theta$ with responsibilities $r_{nk}$,
let $N_k = \sum_n r_{nk}$. The M-step parameters have weights $\pi'_k = N_k / N$, means
$\mu'_k = N_k^{-1} \sum_n r_{nk} x_n$ and covariances
$\Sigma'_k = N_k^{-1} \sum_n r_{nk} (x_n - \mu'_k)(x_n - \mu'_k)^{\top}$. -/
noncomputable def mStep (θ : ValidParams d K) : Params d K where
  weight k := mass xs θ k / N
  mean := newMean xs θ
  cov := newCov xs θ

/-! ## Data in general position -/

variable {xs} in
/-- **Data that span the space affinely.** A family $(x_n)_{n<N}$ of points of $\mathbb{R}^d$
is in general position when it has at least one point ($N > 0$) and is not contained in an
affine hyperplane: for every nonzero $v \in \mathbb{R}^d$ there are indices $n, n'$ with
$\langle v, x_n \rangle \neq \langle v, x_{n'} \rangle$.

On such data every responsibility-weighted sample covariance is positive definite. -/
structure SpansAffinely (xs : Fin N → EuclideanSpace ℝ (Fin d)) : Prop where
  pos : 0 < N
  spans : ∀ v : EuclideanSpace ℝ (Fin d), v ≠ 0 → ∃ n n', ⟪v, xs n⟫ ≠ ⟪v, xs n'⟫

theorem mass_pos (hN : 0 < N) (θ : ValidParams d K) (k : Fin K) : 0 < mass xs θ k :=
  Finset.sum_pos (fun n _ => resp_pos θ (xs n) k) ⟨⟨0, hN⟩, Finset.mem_univ _⟩

theorem sum_mass (θ : ValidParams d K) : ∑ k, mass xs θ k = N := by
  simp only [mass]
  rw [Finset.sum_comm]
  simp [sum_resp]

/-- **The covariance update is positive definite.** Let $(x_n)_{n<N}$ be data in $\mathbb{R}^d$
in general position: $N > 0$, and for every nonzero $v \in \mathbb{R}^d$ the values
$\langle v, x_n \rangle$ are not all equal. Then for all valid parameters $\theta$ of the
$K$-component full-covariance Gaussian mixture and every component $k$, the covariance update
$\Sigma_k'$ (the responsibility-weighted sample covariance of the data about the
responsibility-weighted mean) is positive definite. -/
theorem newCov_posDef {xs : Fin N → EuclideanSpace ℝ (Fin d)} (hx : SpansAffinely xs)
    (θ : ValidParams d K) (k : Fin K) : (newCov xs θ k).PosDef :=
  weightedScatter_posDef (fun n => resp_pos θ (xs n) k) hx.spans _

theorem mStep_valid {xs : Fin N → EuclideanSpace ℝ (Fin d)} (hx : SpansAffinely xs)
    (θ : ValidParams d K) : (mStep xs θ).Valid where
  weight_pos k := div_pos (mass_pos xs hx.pos θ k) (by exact_mod_cast hx.pos)
  weight_sum := by
    simp only [mStep]
    rw [← Finset.sum_div, sum_mass, div_self (by exact_mod_cast hx.pos.ne')]
  cov_posDef k := newCov_posDef hx θ k

/-- **EM step for the full-covariance Gaussian mixture.** For data
$x_1, \dots, x_N \in \mathbb{R}^d$ in general position (at least one point, and not all in an
affine hyperplane) and valid parameters $\theta$, the EM step returns the M-step parameters of
$\theta$: with responsibilities $r_{nk}$ under $\theta$ and $N_k = \sum_n r_{nk}$, the new
weights are $N_k / N$, the new means are the responsibility-weighted means and the new
covariances are the responsibility-weighted sample covariances. General position makes these
parameters valid. -/
noncomputable def emStep (hx : SpansAffinely xs) (θ : ValidParams d K) : ValidParams d K :=
  ⟨mStep xs θ, mStep_valid hx θ⟩

/-! ## The M-step maximizes `Q` -/

/-- **Component term of the EM objective for full-covariance Gaussian mixtures.** Given points
$x_1, \dots, x_N$ of $\mathbb{R}^d$, valid parameters $\theta$ of a $K$-component
full-covariance Gaussian mixture, a component $k$, a mean $\mu \in \mathbb{R}^d$ and a real
$d \times d$ matrix $S$, the component term is
$$
C_k(\mu, S) = \sum_n r_{nk} \log \mathcal{N}(x_n \mid \mu, S),
$$
where $r_{nk}$ is the responsibility of component $k$ for $x_n$ under $\theta$ and
$\mathcal{N}(\cdot \mid \mu, S)$ is the multivariate Gaussian density with mean $\mu$ and
covariance matrix $S$.

The matrix $S$ is not required to be positive definite; the density is defined for every real
matrix. -/
noncomputable def compTerm (θ : ValidParams d K) (k : Fin K) (μ : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ n, resp θ (xs n) k * log (multivariateGaussianPDFReal μ S (xs n))

/-- **The EM objective of a full-covariance Gaussian mixture splits by component.** Let
$x_1, \dots, x_N$ be points of $\mathbb{R}^d$, and let $\theta'$ and $\theta$ be valid parameters
of a $K$-component full-covariance Gaussian mixture, where $\theta'$ has weights $\pi_k'$, means
$\mu_k'$ and covariance matrices $\Sigma_k'$. Then the EM objective of the mixture's joint density
satisfies
$$
Q(\theta' \mid \theta) = \sum_k \bigl(N_k \log \pi_k' + C_k(\mu_k', \Sigma_k')\bigr),
$$
where $r_{nk}$ is the responsibility of component $k$ for $x_n$ under $\theta$,
$N_k = \sum_n r_{nk}$ and $C_k(\mu, S) = \sum_n r_{nk} \log \mathcal{N}(x_n \mid \mu, S)$, with
$\mathcal{N}(\cdot \mid \mu, S)$ the multivariate Gaussian density with mean $\mu$ and covariance
matrix $S$. -/
theorem emQ_eq (θ' θ : ValidParams d K) :
    emQ joint xs θ' θ = ∑ k, (mass xs θ k * log (θ'.1.weight k) +
      compTerm xs θ k (θ'.1.mean k) (θ'.1.cov k)) := by
  have hlog : ∀ n k, log (joint θ' (xs n) k) = log (θ'.1.weight k) +
      log (multivariateGaussianPDFReal (θ'.1.mean k) (θ'.1.cov k) (xs n)) := fun n k =>
    log_mul (θ'.2.weight_pos k).ne' (multivariateGaussianPDFReal_pos _ (θ'.2.cov_posDef k) _).ne'
  simp only [emQ, hlog, mul_add, Finset.sum_add_distrib, mass, compTerm]
  rw [Finset.sum_comm (f := fun n k => posterior joint θ (xs n) k * log (θ'.1.weight k)),
    Finset.sum_comm (f := fun n k => posterior joint θ (xs n) k *
      log (multivariateGaussianPDFReal (θ'.1.mean k) (θ'.1.cov k) (xs n)))]
  simp only [Finset.sum_mul, resp]

/-- **The mean and covariance updates maximize each component term.** Let
$x_1, \dots, x_N \in \mathbb{R}^d$ be data in general position (at least one point, and not all
in an affine hyperplane), let $\theta$ be valid mixture parameters with responsibilities
$r_{nk}$, and fix a component $k$. Write $\mathcal{N}(x \mid \mu, S)$ for the multivariate
Gaussian density and let $\mu'_k$ and $\Sigma'_k$ be the responsibility-weighted mean and the
responsibility-weighted sample covariance of the data for component $k$. Then for every
$\mu \in \mathbb{R}^d$ and every positive definite $d \times d$ matrix $S$,
$$\sum_n r_{nk} \log \mathcal{N}(x_n \mid \mu, S) \le
\sum_n r_{nk} \log \mathcal{N}(x_n \mid \mu'_k, \Sigma'_k).$$ -/
theorem compTerm_le {xs : Fin N → EuclideanSpace ℝ (Fin d)} (hx : SpansAffinely xs)
    (θ : ValidParams d K) (k : Fin K) (μ : EuclideanSpace ℝ (Fin d))
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    compTerm xs θ k μ S ≤ compTerm xs θ k (newMean xs θ k) (newCov xs θ k) := by
  have : Nonempty (Fin N) := ⟨⟨0, hx.pos⟩⟩
  exact sum_mul_log_multivariateGaussianPDFReal_le (fun n => resp_pos θ (xs n) k) hx.spans μ hS

/-- **The weight update maximizes the weights term of the full-covariance mixture.** Let
$(x_n)_{n<N}$ be data in $\mathbb{R}^d$ with $N > 0$, let $\theta$ be valid parameters, and let
$N_k = \sum_n r_{nk}$, where $r_{nk}$ is the responsibility of component $k$ for $x_n$. Then for
all real weights $w_k > 0$ with $\sum_k w_k = 1$,
$$\sum_k N_k \log w_k \le \sum_k N_k \log \frac{N_k}{N}.$$

The proof is Gibbs' inequality. -/
theorem sum_mass_mul_log_le (hN0 : 0 < N) (θ : ValidParams d K) {w : Fin K → ℝ}
    (hw : ∀ k, 0 < w k) (hsum : ∑ k, w k = 1) :
    ∑ k, mass xs θ k * log (w k) ≤ ∑ k, mass xs θ k * log (mass xs θ k / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hN0
  have hq : IsDist fun k => mass xs θ k / N :=
    ⟨fun k => (div_pos (mass_pos xs hN0 θ k) hN).le, by
      rw [← Finset.sum_div, sum_mass, div_self hN.ne']⟩
  have h := sum_mul_log_sub_le hw hq
  rw [hsum, log_one] at h
  have heq : ∑ k, mass xs θ k * log (w k) - ∑ k, mass xs θ k * log (mass xs θ k / N) =
      N * ∑ k, mass xs θ k / N * (log (w k) - log (mass xs θ k / N)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  have : N * ∑ k, mass xs θ k / N * (log (w k) - log (mass xs θ k / N)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hN.le h
  linarith

/-- **The M-step of the full-covariance Gaussian mixture maximizes the EM objective.** Let
$x_1, \dots, x_N \in \mathbb{R}^d$ be data in general position: $N > 0$, and for every nonzero
$v \in \mathbb{R}^d$ the values $\langle v, x_n \rangle$ are not all equal. Let $\theta$ be valid
parameters of a $K$-component full-covariance Gaussian mixture, and let $\theta^+$ be the result
of the EM step applied to $\theta$. Then every valid parameter $\theta'$ satisfies
$Q(\theta' \mid \theta) \le Q(\theta^+ \mid \theta)$, where $Q$ is the EM objective of the
mixture's joint density. -/
theorem emQ_le_emStep (hx : SpansAffinely xs) (θ' θ : ValidParams d K) :
    emQ joint xs θ' θ ≤ emQ joint xs (emStep xs hx θ) θ := by
  rw [emQ_eq, emQ_eq, Finset.sum_add_distrib, Finset.sum_add_distrib]
  exact add_le_add (sum_mass_mul_log_le xs hx.pos θ θ'.2.weight_pos θ'.2.weight_sum)
    (Finset.sum_le_sum fun k _ => compTerm_le hx θ k _ (θ'.2.cov_posDef k))

/-- **Each EM step for the full-covariance Gaussian mixture does not decrease the
log-likelihood.** Let $x_1, \dots, x_N \in \mathbb{R}^d$ be data in general position (at least
one point, and not all in an affine hyperplane) and let $\theta$ be valid parameters. If
$\theta^{+}$ is the result of one EM step from $\theta$, then $\ell(\theta) \le \ell(\theta^{+})$,
where $\ell$ is the log-likelihood of the data under the mixture. -/
theorem logLik_le_emStep (hx : SpansAffinely xs) (θ : ValidParams d K) :
    logLik joint xs θ ≤ logLik joint xs (emStep xs hx θ) := by
  have := nonempty_of_valid θ
  exact logLik_le_of_emQ_le (fun θ x k => joint_pos θ x k) xs (emQ_le_emStep xs hx θ θ)

/-- **The log-likelihood is monotone along the EM iterates of a full-covariance Gaussian
mixture.** Let $x_1, \dots, x_N \in \mathbb{R}^d$ be data in general position: $N > 0$, and for
every nonzero $v \in \mathbb{R}^d$ the values $\langle v, x_n \rangle$ are not all equal. Let
$\theta_0$ be valid parameters of a $K$-component full-covariance Gaussian mixture, and let
$\theta_t$ be the result of $t$ EM steps from $\theta_0$. Then $\ell(\theta_t)$ is nondecreasing
in $t \in \mathbb{N}$, where $\ell$ is the log-likelihood of the data under the mixture's joint
density. -/
theorem logLik_iterate_emStep_monotone (hx : SpansAffinely xs) (θ₀ : ValidParams d K) :
    Monotone fun t => logLik joint xs ((emStep xs hx)^[t] θ₀) := by
  have := nonempty_of_valid θ₀
  exact logLik_iterate_monotone (fun θ x k => joint_pos θ x k) xs
    (fun θ => emQ_le_emStep xs hx θ θ) θ₀

end Cslib.MachineLearning.LatentVariable.GaussianMixtureFullCov
