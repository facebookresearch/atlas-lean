# Tweedie's formula

Let $g$ be a finite nonzero measure on $\mathbb R$, the prior of $\mu$, and let $x \mid \mu \sim \mathcal N(\mu, v)$ with $v > 0$. Write $f$ for the [marginal density](gaussian-mixture-density.md) and $m$ for the [posterior mean](gaussian-posterior-mean.md). Then for every $x \in \mathbb R$,

$$m(x) = x + v\, (\log f)'(x) .$$

The posterior mean is the unbiased estimate $x$ plus a Bayes correction that involves only the marginal density, not the prior. In empirical Bayes work $f$ is estimated from many observations sharing the prior, which avoids deconvolving $f$ to recover $g$.

This is Efron (2011), equation (1.4), $\mathbb E\{\mu \mid z\} = z + \sigma^2 l'(z)$ with $l = \log f$ and $\sigma^2 = v$; Efron attributes it to Robbins (1956), who credits Tweedie. Johnstone's draft states the multivariate unit-variance version as equation (2.26), the Brown–Tweedie formula.

Relation to the sources:

- Efron allows a prior "density" that may include atoms; the statement above takes any finite nonzero measure, with no density and no moment condition.
- The left side is the Bayes ratio. Its identification with a conditional expectation, which needs $\int |\mu|\, g(d\mu) < \infty$, is [Tweedie's formula, conditional expectation form](cond-exp-fst-gaussian-location-joint.md).
- Efron derives (1.4) from the exponential-family form (2.1)–(2.8). A direct proof: by [differentiation under the integral sign](has-deriv-at-gaussian-mixture-density.md), $v f'(x) = \int \mu\, \varphi_v(x - \mu)\, g(d\mu) - x f(x)$, and $f > 0$.

The second-order formula is [Tweedie's formula for the posterior variance](gaussian-posterior-second-moment-sub-sq.md).

## Background

- [Finite-support Tweedie score identity](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/mixture-models/has-gradient-at-log-marginal-joint-of-me.md): the same identity as a finite-sum calculation for a prior with finitely many atoms in $\mathbb R^d$, with scaling $\lambda$.
- [Score and optimal denoiser for Gaussian data](../../../ComputerScience/machine-learning/diffusion-and-flow-generative-models/gaussian-data-score-and-denoiser.md): the identity $x + \sigma^2 \nabla \log p_\sigma(x) = \mathbb E[X_0 \mid X = x]$ checked directly for Gaussian data in $\mathbb R^D$, the form used for denoising in diffusion models.
- [Posterior mean in the normal–normal model](gaussian-posterior-mean-gaussian-real.md): the Gaussian prior, where the formula gives linear shrinkage.

## Sources

- Bradley Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. 106 (2011), no. 496, 1602–1614, DOI 10.1198/jasa.2011.tm11181. Equation numbers are those of the author's manuscript at https://efron.ckirby.su.domains/papers/2011TweediesFormula.pdf.
- Herbert Robbins, *An empirical Bayes approach to statistics*, Proc. Third Berkeley Symp. Math. Statist. Probab., Vol. 1, Univ. California Press (1956), 157–163, which credits the formula to M. K. Tweedie (cited from Efron 2011; not consulted).
- Iain M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, pre-publication draft of 16 September 2019, https://imjohnstone.su.domains/GE_09_16_19.pdf. Numbers refer to that draft.
