# Posterior mean in the Gaussian location model

For a prior $g$ on $\mathbb R$ and a variance $v > 0$, Bayes' rule gives the posterior mean of $\mu$ given $x$ in the model $\mu \sim g$, $x \mid \mu \sim \mathcal N(\mu, v)$ as the ratio

$$m(x) = \frac{\int \mu\, \varphi_v(x - \mu)\, g(d\mu)}{f(x)}, \qquad f(x) = \int \varphi_v(x - \mu)\, g(d\mu) .$$

The ratio does not change when $g$ is multiplied by a positive constant, so the results below allow any finite nonzero $g$. If $f(x) = 0$, the ratio is $0$ by convention (and a non-integrable numerator is read as $0$), but [the marginal density is positive](gaussian-mixture-density-pos.md) as soon as $g \ne 0$ is finite.

For priors with a finite first moment this ratio is a version of the conditional expectation $\mathbb E[\mu \mid x]$: see [Tweedie's formula, conditional expectation form](cond-exp-fst-gaussian-location-joint.md).

## Background

- [Marginal density of a Gaussian location mixture](gaussian-mixture-density.md): the denominator.

## Sources

- Bradley Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. 106 (2011), no. 496, 1602–1614, DOI 10.1198/jasa.2011.tm11181. Equation numbers are those of the author's manuscript at https://efron.ckirby.su.domains/papers/2011TweediesFormula.pdf. The ratio is the left side of equation (1.4).
