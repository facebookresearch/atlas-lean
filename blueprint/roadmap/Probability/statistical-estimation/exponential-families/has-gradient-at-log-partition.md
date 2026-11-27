# The gradient of the log-partition function is the mean parameter

Let $X$ be a finite set, $E$ a real inner product space and $\phi : X \to E$ a sufficient statistic. If $X$ is nonempty and $E$ is complete, then $A$ is differentiable at every $\theta \in E$ with gradient

$$
\nabla A(\theta) = \mathbb E_\theta[\phi(X)] = \sum_{x \in X} p_\theta(x)\,\phi(x) .
$$

So the forward map from canonical to mean parameters is $\theta \mapsto \nabla A(\theta)$, and maximum likelihood in the family is moment matching.

## Informally uses

- [The partition function is positive](partition-sum-pos.md): the chain rule for $\log Z$ at $Z(\theta) > 0$.

## Related topics

- [The gradient of the log-partition function with base weights is the mean](has-gradient-at-log-partition-2.md): the form with base weights $h$ and a statistic in $\mathbb{R}^\iota$, instead of the counting base measure and a statistic in an inner product space.

## Sources

- M. J. Wainwright and M. I. Jordan, *Graphical models, exponential families, and variational inference*, Found. Trends Mach. Learn. 1(1–2) (2008) 1–305, Proposition 3.1(a), first-derivative part, equation (3.41a), with the counting measure (no differentiation under an integral is needed).
