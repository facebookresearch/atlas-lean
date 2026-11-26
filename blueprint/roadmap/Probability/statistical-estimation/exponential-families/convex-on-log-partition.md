# The log-partition function is convex

Let $X$ be a finite set, $E$ a real inner product space and $\phi : X \to E$ a sufficient statistic. If $X$ is nonempty then $A$ is convex on $E$.

Wainwright and Jordan prove this from the Hessian, the covariance matrix of $\phi(X)$. It also follows from the Gibbs variational principle: $A$ is the pointwise maximum over distributions $q$ of the affine functions $\theta \mapsto \langle\mathbb E_q[\phi], \theta\rangle + H(q)$. Strict convexity for minimal representations is not part of this statement.

## Informally uses

- [Gibbs variational principle, upper bound](sum-mul-inner-sub-log-le.md): each affine function lies below $A$.
- [Gibbs variational principle, attainment](sum-density-mul-inner-sub-log.md): equality at $q = p_\theta$, used at the convex combination $\theta = a\theta_1 + b\theta_2$.

## Related topics

- [The log-partition function with base weights is convex](convex-on-log-partition-2.md): the form with base weights $h$ and a statistic in $\mathbb{R}^\iota$, instead of the counting base measure and a statistic in an inner product space.

## Sources

- M. J. Wainwright and M. I. Jordan, *Graphical models, exponential families, and variational inference*, Found. Trends Mach. Learn. 1(1–2) (2008) 1–305, Proposition 3.1(b).
