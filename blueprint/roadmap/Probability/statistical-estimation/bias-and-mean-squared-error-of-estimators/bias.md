# Bias of an estimator

Let $S$ be a measurable space, $W : S \to \mathbb{R}$ an estimator,
$\mu$ a probability measure on $S$ for which $W$ is integrable, and $\theta \in \mathbb{R}$ a
target. The bias of $W$ under $\mu$ at $\theta$ is $\int_S W \, d\mu - \theta$, the expected value
of $W$ under $\mu$ minus $\theta$.

Integrability of $W$ is part of the input: it is the domain on which the expectation exists in
the source (Chapter 2, Definition 2.2.1), so a nonintegrable estimator has no finite bias.

## Sources

- blueprint `af_723199a7ca6fb3e936a73618`.
