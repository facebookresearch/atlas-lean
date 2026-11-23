# Posterior mean in the Poisson model

For a prior $g$ on the rate and a count $x$, consider the Bayes ratio

$$m(x) = \frac{\int \theta\, e^{-\theta} \theta^x / x!\; g(d\theta)}{f(x)},$$

with $f$ the [marginal mass](poisson-mixture-mass.md). When both integrands are $g$-integrable and $f(x) > 0$, Bayes' rule makes $m(x)$ the posterior mean $\mathbb E[\theta \mid x]$ (Efron 2021, equations (1.6)–(1.7)). Otherwise $m(x)$ is fixed by convention: the ratio is $0$ when $f(x) = 0$, and a non-integrable integral is read as $0$; that value is not in general a posterior mean.

## Sources

- Bradley Efron, *Empirical Bayes: concepts and methods*, author's manuscript (2021), https://efron.ckirby.su.domains/papers/2021EB-concepts-methods.pdf.
