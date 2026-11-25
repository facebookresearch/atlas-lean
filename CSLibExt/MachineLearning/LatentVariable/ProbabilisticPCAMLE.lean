/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ProbabilisticPCA
public import MathlibExt.Probability.Distributions.GaussianMLE

/-!
# Probabilistic PCA: the likelihood

Maximum-likelihood facts for probabilistic PCA (Tipping and Bishop, *Probabilistic principal
component analysis*, J. R. Stat. Soc. B 61, 1999; Bishop, *Pattern Recognition and Machine
Learning*, Section 12.2.1), whose observation `x = W z + μ + ε` has law `N(μ, W Wᵀ + σ² I)`
(`ppca_map_eq`, `LatentVariable/ProbabilisticPCA.lean`).

Main results:

* `ppcaCov` (`W Wᵀ + σ² I`), `ppcaCov_posDef`; `ppca_map_eq_withDensity`: **for `σ² > 0` the
  observation has the Gaussian density** `N(x | μ, W Wᵀ + σ² I)`, so `logLik` is its
  log-likelihood.
* `logLik_le_sampleMean`: **the MLE of `μ` is the sample mean**, for every `W` and `σ²`.
* `logLik_le_gaussianMLE`: when the sample covariance is positive definite, the likelihood is at
  most that of the Gaussian with the sample mean and sample covariance (MathlibExt's
  `sum_mul_log_multivariateGaussianPDFReal_le_of_posDef`); `IsMLE`, `isMLE_of_sampleCov_eq`:
  **if the sample covariance has the form `W₀ W₀ᵀ + σ₀² I` with `σ₀² > 0`, then `(x̄, W₀, σ₀²)` is a
  maximum-likelihood estimate**.
* `logLik_zero_le`: with no latent factors (`W = 0`) the MLE of `σ²` is `tr S / d`, for any data
  with a positive total sample variance (rank-deficient data included).

Not covered: Tipping and Bishop's principal-subspace theorem for a general sample covariance
(`W_ML = U_q (Λ_q - σ² I)^{1/2} R`, `σ²_ML` the mean discarded eigenvalue). Its proof combines
von Neumann's trace inequality (MathlibExt's `exists_perm_sum_mul_eigenvalues_le_trace_mul`) with
a constrained optimization over the spectrum of `W Wᵀ + σ² I`; the latter is not done here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LatentVariable.ProbabilisticPCA

open MeasureTheory ProbabilityTheory Matrix WithLp Real MetaMathlibExt
open scoped RealInnerProductSpace

variable {q d N : ℕ}

/-- **Probabilistic PCA covariance.** For a real $d \times q$ matrix $W$ and a real number
$\sigma^2$, the probabilistic PCA covariance is the $d \times d$ matrix $W W^\top + \sigma^2 I$. -/
def ppcaCov (W : Matrix (Fin d) (Fin q) ℝ) (σ2 : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  W * Wᵀ + σ2 • 1

theorem ppcaCov_posDef (W : Matrix (Fin d) (Fin q) ℝ) {σ2 : ℝ} (hσ : 0 < σ2) :
    (ppcaCov W σ2).PosDef := by
  have hWW : (W * Wᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose W
  exact PosDef.posSemidef_add hWW (PosDef.one.smul hσ)

/-- **The density of the probabilistic PCA observation.** Let $z$ and $\varepsilon$ be
independent random vectors on a probability space, with $z$ standard Gaussian in $\mathbb{R}^q$
and $\varepsilon$ Gaussian in $\mathbb{R}^d$ with mean $0$ and covariance $\sigma^2 I$, where
$\sigma^2 > 0$. Then for every real $d \times q$ matrix $W$ and every $\mu \in \mathbb{R}^d$, the
law of $x = W z + \mu + \varepsilon$ has density $\mathcal{N}(x \mid \mu, W W^\top + \sigma^2 I)$
with respect to Lebesgue measure on $\mathbb{R}^d$, where $\mathcal{N}(x \mid \mu, \Sigma)$ is the
multivariate Gaussian density with mean $\mu$ and covariance $\Sigma$. -/
theorem ppca_map_eq_withDensity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → EuclideanSpace ℝ (Fin q)} {E : Ω → EuclideanSpace ℝ (Fin d)}
    {σ2 : ℝ} (hσ : 0 < σ2) (hZ : HasLaw Z (stdGaussian _) P)
    (hE : HasLaw E (multivariateGaussian 0 (σ2 • 1)) P) (hind : IndepFun Z E P)
    (W : Matrix (Fin d) (Fin q) ℝ) (μ : EuclideanSpace ℝ (Fin d)) :
    P.map (fun ω => toEuclideanLin W (Z ω) + μ + E ω) =
      volume.withDensity fun x =>
        ENNReal.ofReal (multivariateGaussianPDFReal μ (ppcaCov W σ2) x) := by
  rw [ppca_map_eq hσ.le hZ hE hind W μ]
  exact multivariateGaussian_eq_withDensity μ (ppcaCov_posDef W hσ)

/-- **Probabilistic PCA log-likelihood.** For data $x_1, \dots, x_N \in \mathbb{R}^d$, a mean
$\mu \in \mathbb{R}^d$, a real $d \times q$ loading matrix $W$ and a real number $\sigma^2$, the
probabilistic PCA log-likelihood of the data is
$$
\sum_{n=1}^N \log \mathcal{N}(x_n \mid \mu, W W^\top + \sigma^2 I),
$$
where, for a real $d \times d$ matrix $\Sigma$ and $x \in \mathbb{R}^d$,
$$
\mathcal{N}(x \mid \mu, \Sigma) = (2\pi)^{-d/2} \bigl(\sqrt{\det \Sigma}\bigr)^{-1}
\exp\bigl(-\tfrac{1}{2} (x - \mu)^\top \Sigma^{-1} (x - \mu)\bigr)
$$
is the multivariate Gaussian density formula, read with the conventions $\sqrt{t} = 0$ for
$t < 0$, $0^{-1} = 0$, $\Sigma^{-1} = 0$ for singular $\Sigma$ and $\log 0 = 0$. These conventions
matter only when $W W^\top + \sigma^2 I$ is not positive definite. When $\sigma^2 > 0$ the matrix
$W W^\top + \sigma^2 I$ is positive definite, and this is the density of the Gaussian with mean
$\mu$ and covariance $W W^\top + \sigma^2 I$. -/
noncomputable def logLik (xs : Fin N → EuclideanSpace ℝ (Fin d)) (μ : EuclideanSpace ℝ (Fin d))
    (W : Matrix (Fin d) (Fin q) ℝ) (σ2 : ℝ) : ℝ :=
  ∑ n, log (multivariateGaussianPDFReal μ (ppcaCov W σ2) (xs n))

/-- **Sample mean.** For data points $x_1, \dots, x_N \in \mathbb{R}^d$, the sample mean is
$\bar x = \frac{1}{N} \sum_{n=1}^{N} x_n \in \mathbb{R}^d$.

When $N = 0$ the sample mean is $0$. -/
noncomputable abbrev sampleMean (xs : Fin N → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  weightedMean 1 xs

/-- **Sample covariance.** For data $x_1, \dots, x_N \in \mathbb{R}^d$ with sample mean
$\bar{x}$, the sample covariance is the $d \times d$ matrix
$S = \frac{1}{N} \sum_{n=1}^N (x_n - \bar{x})(x_n - \bar{x})^\top$, taken to be $0$ when
$N = 0$. -/
noncomputable abbrev sampleCov (xs : Fin N → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  weightedScatter 1 xs (sampleMean xs)

/-- **The log-likelihood of no data is zero.** For the empty data set ($N = 0$), the
probabilistic PCA log-likelihood at every $\mu \in \mathbb{R}^d$, every real $d \times q$ matrix
$W$ and every real number $\sigma^2$ is $0$. -/
theorem logLik_of_N_eq_zero (hN : N = 0) (xs : Fin N → EuclideanSpace ℝ (Fin d))
    (μ : EuclideanSpace ℝ (Fin d)) (W : Matrix (Fin d) (Fin q) ℝ) (σ2 : ℝ) :
    logLik xs μ W σ2 = 0 := by
  subst hN
  simp [logLik]

/-- **The mean MLE is the sample mean.** Let $x_1, \dots, x_N \in \mathbb{R}^d$ be data with
sample mean $\bar{x}$. For every $\mu \in \mathbb{R}^d$, every real $d \times q$ loading matrix
$W$ and every real $\sigma^2 > 0$, the probabilistic PCA log-likelihood of the data at
$(\mu, W, \sigma^2)$ is at most its value at $(\bar{x}, W, \sigma^2)$. -/
theorem logLik_le_sampleMean (xs : Fin N → EuclideanSpace ℝ (Fin d))
    (μ : EuclideanSpace ℝ (Fin d)) (W : Matrix (Fin d) (Fin q) ℝ) {σ2 : ℝ} (hσ : 0 < σ2) :
    logLik xs μ W σ2 ≤ logLik xs (sampleMean xs) W σ2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rw [logLik_of_N_eq_zero hN, logLik_of_N_eq_zero hN]
  have hw : 0 < ∑ n, (1 : Fin N → ℝ) n := by simp [hN]
  simpa [logLik] using
    sum_mul_log_multivariateGaussianPDFReal_le_weightedMean hw xs μ (ppcaCov_posDef W hσ)

/-- **The probabilistic PCA likelihood is at most the unconstrained Gaussian maximum.** Let
$x_1, \dots, x_N \in \mathbb{R}^d$ be data whose sample covariance $S$ is positive definite, and
let $\bar{x}$ be their sample mean. Then for every $\mu \in \mathbb{R}^d$, every real
$d \times q$ matrix $W$ and every real $\sigma^2 > 0$, the probabilistic PCA log-likelihood of the
data at $(\mu, W, \sigma^2)$ is at most $\sum_{n=1}^N \log \mathcal{N}(x_n \mid \bar{x}, S)$,
where $\mathcal{N}(x \mid \bar{x}, S)$ is the multivariate Gaussian density with mean $\bar{x}$
and covariance $S$.

The sample covariance is positive definite, for example, when the data do not all lie in an
affine hyperplane. -/
theorem logLik_le_gaussianMLE {xs : Fin N → EuclideanSpace ℝ (Fin d)}
    (hS : (sampleCov xs).PosDef) (μ : EuclideanSpace ℝ (Fin d)) (W : Matrix (Fin d) (Fin q) ℝ)
    {σ2 : ℝ} (hσ : 0 < σ2) :
    logLik xs μ W σ2 ≤
      ∑ n, log (multivariateGaussianPDFReal (sampleMean xs) (sampleCov xs) (xs n)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [logLik]
  have hw : 0 < ∑ n, (1 : Fin N → ℝ) n := by simp [hN]
  simpa [logLik] using sum_mul_log_multivariateGaussianPDFReal_le_of_posDef hw hS μ
    (ppcaCov_posDef W hσ)

/-- **Probabilistic PCA maximum-likelihood estimate.** Given data
$x_1, \dots, x_N \in \mathbb{R}^d$, a triple $(\mu_0, W_0, \sigma_0^2)$ of a mean
$\mu_0 \in \mathbb{R}^d$, a real $d \times q$ loading matrix $W_0$ and a real number $\sigma_0^2$
is a probabilistic PCA maximum-likelihood estimate when $\sigma_0^2 > 0$ and, for every
$\mu \in \mathbb{R}^d$, every real $d \times q$ matrix $W$ and every real $\sigma^2 > 0$, the
probabilistic PCA log-likelihood of the data at $(\mu, W, \sigma^2)$ is at most its value at
$(\mu_0, W_0, \sigma_0^2)$. -/
def IsMLE (xs : Fin N → EuclideanSpace ℝ (Fin d)) (μ₀ : EuclideanSpace ℝ (Fin d))
    (W₀ : Matrix (Fin d) (Fin q) ℝ) (σ₀2 : ℝ) : Prop :=
  0 < σ₀2 ∧ ∀ (μ : EuclideanSpace ℝ (Fin d)) (W : Matrix (Fin d) (Fin q) ℝ) (σ2 : ℝ), 0 < σ2 →
    logLik xs μ W σ2 ≤ logLik xs μ₀ W₀ σ₀2

/-- **Probabilistic PCA MLE when the sample covariance has the model form.** Let
$x_1, \dots, x_N \in \mathbb{R}^d$ be data with sample mean $\bar{x}$ and sample covariance $S$.
If $W_0$ is a real $d \times q$ matrix and $\sigma_0^2 > 0$ is a real number with
$S = W_0 W_0^\top + \sigma_0^2 I$, then $(\bar{x}, W_0, \sigma_0^2)$ is a probabilistic PCA
maximum-likelihood estimate for the data. -/
theorem isMLE_of_sampleCov_eq {xs : Fin N → EuclideanSpace ℝ (Fin d)}
    {W₀ : Matrix (Fin d) (Fin q) ℝ} {σ₀2 : ℝ} (hσ₀ : 0 < σ₀2)
    (h : sampleCov xs = ppcaCov W₀ σ₀2) : IsMLE xs (sampleMean xs) W₀ σ₀2 := by
  refine ⟨hσ₀, fun μ W σ2 hσ => ?_⟩
  have := logLik_le_gaussianMLE (h ▸ ppcaCov_posDef W₀ hσ₀) μ W hσ
  rwa [h] at this

/-- **No latent factors: the noise-variance MLE is the average sample variance.** Let
$x_1, \dots, x_N \in \mathbb{R}^d$ be data with sample mean $\bar{x}$ and sample covariance $S$,
and suppose $\operatorname{tr} S > 0$. Then for every $\mu \in \mathbb{R}^d$ and every real
$\sigma^2 > 0$, the probabilistic PCA log-likelihood of the data with the zero $d \times q$
loading matrix at $(\mu, 0, \sigma^2)$ is at most its value at
$(\bar{x}, 0, \operatorname{tr} S / d)$.

Here $\operatorname{tr} S / d$ is the average sample variance (Tipping and Bishop's $\sigma^2$
estimate with no retained components). -/
theorem logLik_zero_le {xs : Fin N → EuclideanSpace ℝ (Fin d)}
    (hT : 0 < (sampleCov xs).trace) (μ : EuclideanSpace ℝ (Fin d)) {σ2 : ℝ} (hσ : 0 < σ2) :
    logLik xs μ (0 : Matrix (Fin d) (Fin q) ℝ) σ2 ≤
      logLik xs (sampleMean xs) (0 : Matrix (Fin d) (Fin q) ℝ) ((sampleCov xs).trace / d) := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by subst h; simp [weightedScatter] at hT
  have hw : 0 < ∑ n, (1 : Fin N → ℝ) n := by simp [hN]
  have hd : 0 < d := Nat.pos_of_ne_zero fun h => by subst h; simp at hT
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set T := (sampleCov xs).trace with hTdef
  have hTpos : 0 < T := hT
  have hs : 0 < T / d := div_pos hTpos hd'
  -- the log-likelihood of `N(x̄, s I)`
  have hcov : ∀ s : ℝ, ppcaCov (0 : Matrix (Fin d) (Fin q) ℝ) s = s • 1 := fun s => by
    simp [ppcaCov]
  have hval : ∀ {s : ℝ}, 0 < s → logLik xs (sampleMean xs) (0 : Matrix (Fin d) (Fin q) ℝ) s =
      -((N : ℝ) / 2) * (d * log (2 * π) + d * log s + T / s) := by
    intro s hs
    have hinv : (s • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = s⁻¹ • 1 :=
      inv_eq_left_inv (by rw [smul_mul_smul, Matrix.one_mul, inv_mul_cancel₀ hs.ne', one_smul])
    have h := sum_mul_log_multivariateGaussianPDFReal_eq hw.ne' xs (sampleMean xs)
      (ppcaCov_posDef (0 : Matrix (Fin d) (Fin q) ℝ) hs)
    simp only [Pi.one_apply, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h
    rw [logLik, h, hcov, hinv, det_smul, det_one, mul_one, Fintype.card_fin, log_pow,
      Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul, ← hTdef]
    ring
  refine (logLik_le_sampleMean xs μ _ hσ).trans ?_
  rw [hval hσ, hval hs]
  -- `d log s + T / s ≥ d log (T / d) + d`
  have hlog := log_le_sub_one_of_pos (div_pos hTpos (mul_pos hd' hσ))
  rw [log_div hTpos.ne' (mul_pos hd' hσ).ne', log_mul hd'.ne' hσ.ne'] at hlog
  have e2 : T / (T / d) = d := by field_simp
  rw [log_div hTpos.ne' hd'.ne', e2]
  have hN' : (0 : ℝ) ≤ N / 2 := by positivity
  have key : d * (log T - log d) + d ≤ d * log σ2 + T / σ2 := by
    have := mul_le_mul_of_nonneg_left hlog hd'.le
    have e : d * (T / (d * σ2) - 1) = T / σ2 - d := by field_simp
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hN']

end Cslib.MachineLearning.LatentVariable.ProbabilisticPCA
