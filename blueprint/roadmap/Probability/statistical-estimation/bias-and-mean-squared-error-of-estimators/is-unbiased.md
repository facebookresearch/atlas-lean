# Unbiased estimator

Let $(P_\theta)_{\theta \in \Theta}$ be a family of probability measures
on a measurable space $S$ and $\tau : \Theta \to \mathbb{R}$ a target function. An estimator
$W : S \to \mathbb{R}$ is unbiased for $\tau$ if for every $\theta \in \Theta$ the function $W$ is
$P_\theta$-integrable and $\int_S W \, dP_\theta = \tau(\theta)$.

Integrability is part of the definition, so a non-integrable estimator is never unbiased. The
estimator $W$ is fixed and does not depend on $\theta$.

## Sources

- Casella–Berger Definition 7.3.2 is the case $\tau(\theta) = \theta$ on real parameters; the general target follows section 7.3.2. Blueprint `af_95118d196fd6478105a6eb43`.
