# Marginal mass of a Poisson mixture

For a prior $g$ on the rate $\theta \ge 0$, the marginal mass of a count $x \in \mathbb N$ is

$$f(x) = \int_0^\infty \frac{e^{-\theta} \theta^x}{x!}\, g(d\theta),$$

where $g$ is any measure on $[0, \infty)$. When the integrand is $g$-integrable this is an unnormalised marginal mass; when $g$ is a probability measure it is the probability of $x$ when $\theta \sim g$ and $x \mid \theta \sim \text{Poisson}(\theta)$ (Efron 2021, equations (1.5)–(1.6)). A non-integrable integrand gives the value $0$ by convention, which is not a marginal mass.

## Sources

- Bradley Efron, *Empirical Bayes: concepts and methods*, author's manuscript (2021), https://efron.ckirby.su.domains/papers/2021EB-concepts-methods.pdf.
