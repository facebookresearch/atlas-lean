# Posterior second moment in the Gaussian location model

For a prior $g$ and a variance $v > 0$, the posterior second moment of $\mu$ given $x$ is the Bayes ratio

$$\frac{\int \mu^2\, \varphi_v(x - \mu)\, g(d\mu)}{f(x)},$$

with $f$ the [marginal density](gaussian-mixture-density.md). With the [posterior mean](gaussian-posterior-mean.md) it gives the posterior variance used in [Tweedie's formula for the posterior variance](gaussian-posterior-second-moment-sub-sq.md).

## Sources

- Bradley Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. 106 (2011), no. 496, 1602–1614, DOI 10.1198/jasa.2011.tm11181. Equation numbers are those of the author's manuscript at https://efron.ckirby.su.domains/papers/2011TweediesFormula.pdf. The posterior variance is the second component of equation (2.8).
