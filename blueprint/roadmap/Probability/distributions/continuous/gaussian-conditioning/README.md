# Conditioning of Gaussian vectors

Let $\iota$ and $\kappa$ be finite index sets and let $V = (X, Y)$ be a measurable random vector on a probability space with values in $\mathbb{R}^{\iota \sqcup \kappa}$, with blocks $X \in \mathbb{R}^\iota$ and $Y \in \mathbb{R}^\kappa$. Suppose $V$ has the Gaussian law $N(\mu, S)$ with $S$ positive semidefinite. Write $\mu_X, \mu_Y$ for the blocks of $\mu$ and $S_{11}, S_{12}, S_{21}, S_{22}$ for the blocks of $S$ indexed by $\iota \times \iota$, $\iota \times \kappa$, $\kappa \times \iota$ and $\kappa \times \kappa$, and suppose $S_{22}$ is invertible. Then for almost every $y$ with respect to the law of $Y$, the conditional distribution of $X$ given $Y = y$ is the Gaussian law $N\bigl(\mu_X + S_{12} S_{22}^{-1} (y - \mu_Y),\ S_{11} - S_{12} S_{22}^{-1} S_{21}\bigr)$.

## Idea

Conditioning a Gaussian vector on some of its coordinates gives a Gaussian law again. Its mean is an affine function of the observed value, the best linear predictor. Its covariance, the Schur complement $S_{11} - S_{12} S_{22}^{-1} S_{21}$, does not depend on what was observed. To see why, take $A = S_{12} S_{22}^{-1}$. The residual $X - AY$ is uncorrelated with $Y$, and for jointly Gaussian vectors uncorrelated means independent. Given $Y = y$, $X$ is therefore $Ay$ plus an independent Gaussian vector with mean $\mu_X - A\mu_Y$ and covariance the Schur complement. This formula underlies Kalman filtering and Gaussian process regression. Together with the linear-Gaussian marginal it gives Bayes' theorem for linear observations with Gaussian noise.

## Statements

- [Gaussian conditioning (Schur complement)](cond-distrib-multivariate-gaussian.md)
- [Gaussian conditioning](cond-distrib-of-has-gaussian-law.md): general Gaussian-law form
- [Conditioning on a signal observed in independent additive noise](cond-distrib-add-of-indep-fun.md): signal in independent additive noise
- [Bayes' theorem for a linear-Gaussian observation](cond-distrib-linear-add-of-indep-fun.md): linear-Gaussian Bayes theorem
- [Bayes' theorem for a linear-Gaussian observation, precision form](cond-distrib-linear-add-of-indep-fun-pre.md): precision form
- [The marginal of a linear-Gaussian model](map-linear-add-of-indep-fun.md): marginal of a linear-Gaussian model
- [The additive-noise kernel](noise-kernel.md): definition used in the proof of the main statement
- [Horizontal block matrix](block-row.md): definition used in the main statement
- [Covariances of linear functionals of a Gaussian vector](covariance-inner-of-map-eq.md): lemma used in the proof of the main statement
- [Translating a multivariate Gaussian](map-add-multivariate-gaussian.md): lemma used in the proof of the main statement
- [Linear images of multivariate Gaussians](map-to-euclidean-lin-multivariate-gaussi.md): lemma used in the proof of the main statement
- [Concatenation of independent Gaussian random vectors](map-sum-equiv-prod-symm-of-indep-fun.md): lemma used for the linear-Gaussian forms
- [Independent Gaussian blocks](map-sum-equiv-prod-symm-prod-multivariat.md): lemma used for the linear-Gaussian forms
- [Characteristic function of a product of blocks](char-fun-map-sum-equiv-prod-symm-prod.md): lemma used for the linear-Gaussian forms
- [The inner product splits over blocks](inner-sum-equiv-prod-symm.md): lemma used for the linear-Gaussian forms
- [Block-triangular congruence of a block-diagonal matrix](from-blocks-one-zero-mul-mul-transpose.md): matrix lemma used for the linear-Gaussian forms
- [Block-diagonal matrices with positive semidefinite blocks](pos-semidef-from-blocks-zero.md): matrix lemma used for the linear-Gaussian forms
- [The joint covariance of a linear-Gaussian model is positive semidefinite](pos-semidef-from-blocks-linear.md): matrix lemma used for the linear-Gaussian forms
- [The posterior covariance is positive semidefinite](pos-semidef-sub-mul-inv-mul.md): basic property: the posterior covariance is positive semidefinite

## Background

- [Regular conditional distributions](../../../foundations/regular-conditional-distributions/README.md)

## Related topics

- [Gaussian process regression](../../../../ComputerScience/machine-learning/supervised-learning/gaussian-process-regression/README.md): the Gaussian-process posterior and marginal likelihood as instances of conditioning and linear-Gaussian marginals.
- [Kalman filter](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/README.md): sequential conditioning in a linear-Gaussian state-space model.
- [Bayesian inverse problems](../../../bayesian-statistics/bayesian-inverse-problems/README.md): the linear-Gaussian case of Bayesian inversion, where the posterior is given by this formula.
