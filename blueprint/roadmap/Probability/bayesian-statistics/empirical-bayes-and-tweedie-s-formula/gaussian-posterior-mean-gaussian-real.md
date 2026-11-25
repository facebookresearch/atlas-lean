# Posterior mean in the normal–normal model

For the prior $\mu \sim \mathcal N(0, A)$ with $A \ge 0$ and $x \mid \mu \sim \mathcal N(\mu, v)$ with $v > 0$, the [posterior mean](gaussian-posterior-mean.md) is

$$\mathbb E[\mu \mid x] = \frac{A}{A + v}\, x \qquad \text{for every } x .$$

This is Efron (2021), equation (3.10), $\hat\theta^{\text{Bayes}} = M + B(x - M)$ with $B = A/(A + \sigma_0^2)$, in the case $M = 0$, $\sigma_0^2 = v$; a nonzero prior mean $M$ is not covered. With $v = 1$ and $V = A + 1$ the factor is $1 - 1/V$, Efron (2011), equation (3.8). Estimating $1/V$ without bias by $(N - 2)/\sum_j z_j^2$ turns this Bayes rule into the James–Stein estimator: see [the James–Stein shrinkage factor estimates $1/V$ without bias](../../statistical-estimation/stein-s-lemma-and-james-stein-estimation/integral-james-stein-factor-pi-gaussian.md). The case $A = 0$, a point mass at $0$, gives $\mathbb E[\mu \mid x] = 0$.

The proof applies Stein's lemma to the prior: $\int \mu\, \varphi_v(x - \mu)\, \mathcal N(0, A)(d\mu) = A \int \frac{x - \mu}{v}\, \varphi_v(x - \mu)\, \mathcal N(0, A)(d\mu)$, which is linear in the numerator and the marginal density.

## Informally uses

- [Tweedie's formula](gaussian-posterior-mean-eq-add-mul-deriv.md): Efron (2011) derives (3.8) from it, with the marginal $\mathcal N(0, V)$ and $l'(z) = -z/V$.

## Background

- [Stein's lemma](../../statistical-estimation/stein-s-lemma-and-james-stein-estimation/integrable-and-integral-sub-mul-gaussian.md): the identity used in the proof above instead of Tweedie's formula.
- [Posterior mean of the Normal–Normal model](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/conjugate-priors/normal-post-mean.md): the conjugate posterior mean $(v m_0 + v_0 x)/(v_0 + v)$ with a general prior mean; [the bridge](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/conjugate-priors/gaussian-posterior-mean-gaussian-real-eq.md) shows the two agree when $m_0 = 0$.

## Sources

- Bradley Efron, *Empirical Bayes: concepts and methods*, author's manuscript (2021), https://efron.ckirby.su.domains/papers/2021EB-concepts-methods.pdf.
- Bradley Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. 106 (2011), no. 496, 1602–1614, DOI 10.1198/jasa.2011.tm11181. Equation numbers are those of the author's manuscript at https://efron.ckirby.su.domains/papers/2011TweediesFormula.pdf.
