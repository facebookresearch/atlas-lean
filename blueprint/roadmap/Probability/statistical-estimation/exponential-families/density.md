# Density of a finite exponential family

Let $X$ be a nonempty finite set, $E$ a real inner product space and $\phi : X \to E$ a sufficient statistic. The exponential family with canonical parameter $\theta \in E$ is

$$
p_\theta(x) = \frac{\exp\langle\phi(x), \theta\rangle}{Z(\theta)} = \exp\bigl(\langle\phi(x), \theta\rangle - A(\theta)\bigr), \qquad x \in X .
$$

## Background

- [Log-partition function](log-partition.md): the normalizing constant $A(\theta) = \log Z(\theta)$.

## Related topics

- [Density of an exponential family with base weights](density-2.md): the form with base weights $h$ and a statistic in $\mathbb{R}^\iota$, instead of the counting base measure and a statistic in an inner product space.

## Sources

- M. J. Wainwright and M. I. Jordan, *Graphical models, exponential families, and variational inference*, Found. Trends Mach. Learn. 1(1–2) (2008) 1–305, Section 3.2.
