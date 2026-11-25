# Score and optimal denoiser for Gaussian data

Let $D \ge 1$, let $\mu \in \mathbb{R}^D$ and let $\Sigma$ be a real symmetric positive
semidefinite $D \times D$ matrix, possibly singular. Let $X_0 \sim \mathcal{N}(\mu, \Sigma)$ and
$\varepsilon \sim \mathcal{N}(0, I)$ be independent random vectors in $\mathbb{R}^D$, let
$\sigma > 0$, and let $X = X_0 + \sigma \varepsilon$. Write $C = \Sigma + \sigma^2 I$. Since
$\Sigma$ is positive semidefinite and $\sigma > 0$, $C$ is positive definite, hence invertible.
Then:

- (a) $X \sim \mathcal{N}(\mu, C)$.
- (b) Let $p_\sigma$ be the continuous density of $X$, the Gaussian density with mean $\mu$ and
  covariance $C$. For every $x$, $\nabla \log p_\sigma(x) = -C^{-1} (x - \mu)$. A density is
  only determined up to a Lebesgue-null set; the statement is about the continuous one.
- (c) For almost every $x$ with respect to the law of $X$, the conditional distribution of $X_0$
  given $X = x$ is the Gaussian with mean $\mu + \Sigma C^{-1} (x - \mu)$ and covariance
  $\Sigma - \Sigma C^{-1} \Sigma = \sigma^2 \Sigma C^{-1}$. The law of $X$ has an everywhere
  positive density, so this is the same as Lebesgue-almost every $x$. Taking means, the
  conditional expectation, which is the optimal denoiser in the mean-squared sense, is
  $\mathbb{E}[X_0 \mid X = x] = \mu + \Sigma C^{-1} (x - \mu)$ for almost every $x$. Passing from
  the conditional distribution to the conditional expectation is one further measure-theoretic
  step: the conditional expectation of the integrable vector $X_0$ is, almost surely, the mean of
  its conditional distribution.
- (d) For every $x$, $x + \sigma^2 \bigl(-C^{-1} (x - \mu)\bigr) = \mu + \Sigma C^{-1} (x - \mu)$,
  so by (b) and (c), $x + \sigma^2 \nabla \log p_\sigma(x) = \mathbb{E}[X_0 \mid X = x]$ for
  almost every $x$. This is checked directly for Gaussian data; it is not the general Tweedie
  formula.

Proof: (a) is the marginal of a linear-Gaussian model with $F = I$, $x = X_0$ and
$w = \sigma \varepsilon$, whose law $\mathcal{N}(0, \sigma^2 I)$ is the image of
$\mathcal{N}(0, I)$ under multiplication by $\sigma$; $\sigma \varepsilon$ is independent of
$X_0$ because $\varepsilon$ is. (b) The logarithm of the Gaussian density with positive definite
covariance $C$ is $-\tfrac{1}{2} (x - \mu)^{\mathsf{T}} C^{-1} (x - \mu)$ plus a constant, and
its gradient is $-C^{-1} (x - \mu)$ because $C^{-1}$ is symmetric; this differentiation is a
calculus step. (c) is Bayes' theorem for a linear-Gaussian observation with $H = I$,
$S = \Sigma$ and $R = \sigma^2 I$; its hypothesis that $H S H^{\mathsf{T}} + R = C$ is invertible
holds because $\sigma > 0$, and fails at $\sigma = 0$ when $\Sigma$ is singular. The covariance
identity is $\Sigma - \Sigma C^{-1} \Sigma = \Sigma C^{-1} (C - \Sigma) = \sigma^2 \Sigma C^{-1}$,
using that $\Sigma$ and $C$ commute. (d) $I - \sigma^2 C^{-1} = (C - \sigma^2 I) C^{-1} =
\Sigma C^{-1}$.

Spectral form: let $u_1, \dots, u_D$ be a real orthonormal basis of eigenvectors of $\Sigma$,
with $\Sigma u_k = \lambda_k u_k$ and $\lambda_k \ge 0$, zero eigenvalues included. Then
$C^{-1} = \sum_{k=1}^{D} (\lambda_k + \sigma^2)^{-1} u_k u_k^{\mathsf{T}}$ and
$\Sigma C^{-1} = \sum_{k=1}^{D} \frac{\lambda_k}{\lambda_k + \sigma^2} u_k u_k^{\mathsf{T}}$, so

$$\nabla \log p_\sigma(x) = -\sum_{k=1}^{D} \frac{\langle u_k, x - \mu \rangle}{\lambda_k + \sigma^2} u_k,
\qquad
\mathbb{E}[X_0 \mid X = x] = \mu + \sum_{k=1}^{D} \frac{\lambda_k}{\lambda_k + \sigma^2} \langle u_k, x - \mu \rangle u_k,$$

the second for almost every $x$. A direction with $\lambda_k = 0$ contributes
$-\sigma^{-2} \langle u_k, x - \mu \rangle u_k$ to the score and nothing to the denoiser. Wang and
Vastola write the same formulas with the $D \times r$ matrix $U$ of the eigenvectors with
$\lambda_k > 0$ and $\tilde{\Lambda}_\sigma = \operatorname{diag}(\lambda_k / (\lambda_k + \sigma^2))$
over those $k$; since $\sum_{\lambda_k = 0} u_k u_k^{\mathsf{T}} = I - U U^{\mathsf{T}}$, the score
is $-\sigma^{-2} (I - U \tilde{\Lambda}_\sigma U^{\mathsf{T}}) (x - \mu)$. The basis-free
statements above need no eigenbasis, and the Woodbury identity is not needed in either form.

## Informally uses

- [The marginal of a linear-Gaussian model](../../../Probability/distributions/continuous/gaussian-conditioning/map-linear-add-of-indep-fun.md):
  mathematical prerequisite, (a) with $F = I$, $x = X_0$, $S = \Sigma$, $w = \sigma \varepsilon$,
  $c = 0$ and $Q = \sigma^2 I$.
- [Bayes' theorem for a linear-Gaussian observation](../../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-linear-add-of-indep-fun.md):
  mathematical prerequisite, (c) with $H = I$, $S = \Sigma$ and $R = \sigma^2 I$; its
  invertibility hypothesis is where $\sigma > 0$ is used.
- [The multivariate Gaussian density](../../../Probability/distributions/continuous/multivariate-normal-distribution/gaussian-density/multivariate-gaussian-eq-with-density.md):
  mathematical prerequisite, the density in (b), for the positive definite covariance
  $\Sigma + \sigma^2 I$; the gradient of its logarithm is a further calculus step.

## Background

- [Tweedie's formula](../../../Probability/bayesian-statistics/empirical-bayes-and-tweedie-s-formula/gaussian-posterior-mean-eq-add-mul-deriv.md):
  background, the general formula $\mathbb E[\mu \mid x] = x + \sigma^2 (\log f)'(x)$ for an arbitrary prior, proved in dimension one; (d) above is its Gaussian-data case in dimension $D$.
- [The quadratic form of a symmetric matrix in an orthonormal eigenbasis](../../../LinearAlgebra/positive-definite-matrices/von-neumann-s-trace-inequality/inner-to-euclidean-lin-self-eq-sum.md):
  background, it uses the real orthonormal eigenbasis of a real symmetric matrix from the spectral
  theorem, which is the basis in the spectral form above; the basis-free statements do not need it.
- [The probabilistic PCA marginal](../unsupervised-learning/probabilistic-principal-component-analysis/ppca-map-eq.md):
  background, an alternative route to (a) when $X_0$ is written as $W Z + \mu$ with
  $W W^{\mathsf{T}} = \Sigma$, for instance $W = U \Lambda^{1/2}$, and noise variance $\sigma^2$.
- [Finite-support Tweedie score identity](../bayesian-inference-and-sampling/mixture-models/has-gradient-at-log-marginal-joint-of-me.md):
  background, the score identity $\nabla \log p(z) = (\lambda m(z) - z) / \sigma^2$ for data taking
  finitely many values, with $m(z)$ the posterior-weighted mean of those values, a
  finite-sum calculation. It does not cover the Gaussian data on this page.

## Sources

- B. Wang and J. J. Vastola, "The Unreasonable Effectiveness of Gaussian Score Approximation for Diffusion Models and its Applications", arXiv:2412.09726 (version 1), Section 2.2, equations (5) and (6) (score and optimal denoiser of the Gaussian model, with $\Sigma$ of rank $r \le D$), and Section 3.1, equations (12) and (13) (the form with the $D \times r$ eigenvector matrix).
- AI-authored exposition.
