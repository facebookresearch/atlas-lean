# Canonical joint law of `(X, H X + Z)`

Let $(\Omega, \mu)$ be a probability space, let $\iota$ and $\kappa$ be finite index sets, $H \in \mathbb{R}^{\iota \times \kappa}$, and $R \in \mathbb{R}^{\iota \times \iota}$. Let $X : \Omega \to \mathbb{R}^\kappa$ and $Z : \Omega \to \mathbb{R}^\iota$ be measurable and independent, with $Z \sim \mathcal{N}(0, R)$. Then the joint law of $(X, HX + Z)$ is the law of $X$ composed with the additive-noise kernel $N_H$ that sends $x$ to the law of $Hx + Z'$ with $Z' \sim \mathcal{N}(0, R)$:

$$(X, HX + Z)_\ast \mu = X_\ast\mu \otimes N_H.$$

$\mathcal{N}(m, S)$ is Mathlib's Gaussian with mean $m$ and covariance parameter $S$, which is the point mass $\delta_m$ when $S$ is not positive semidefinite; the statement holds for every real matrix $R$.
