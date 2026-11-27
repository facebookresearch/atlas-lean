# Garwood's exact Poisson confidence bound

Let $0 < \alpha < 1$. For an observed count $k \in \mathbb{N}$, Garwood's upper confidence bound is $u_\alpha(k) = \sup\{x \ge 0 : F_k(x) \ge \alpha\}$, where $F_k(x) = \sum_{j=0}^{k} e^{-x} x^j / j!$ is the Poisson distribution function; it is the root of $F_k(u) = \alpha$. For every mean $r \ge 0$, if $K$ has the Poisson law with mean $r$, then $P\bigl(r \le u_\alpha(K)\bigr) \ge 1 - \alpha$: the bound covers the true mean with probability at least $1 - \alpha$.

## Idea

The bound inverts a test. After observing $k$, a mean $x$ is rejected when $F_k(x) < \alpha$, that is, when a count as small as $k$ would be unlikely under mean $x$. The bound $u_\alpha(k)$ is the largest mean that is not rejected. Coverage fails only when $F_K(r) < \alpha$, and for a discrete variable this transform is super-uniform: $P(F_K(r) \le \alpha) \le \alpha$. Discreteness makes the coverage conservative rather than equal to $1 - \alpha$. "Exact" means that the bound uses the Poisson law itself, not a normal approximation. By Poisson–gamma duality, $u_\alpha(k)$ is the $(1 - \alpha)$-quantile of the gamma law with shape $k + 1$ and rate $1$. After observing $0$ it is $\log(1/\alpha)$, about $3.0$ for $\alpha = 0.05$.

## Statements

- [Exact coverage of Garwood's bound](garwood-upper-coverage.md)
- [Garwood's exact upper confidence bound](garwood-upper.md): definition used in the main statement
- [Garwood upper bound solves the distribution function equation](poisson-cdf-garwood-upper.md): basic property: the bound solves its defining equation
- [Positivity of the Garwood upper bound](garwood-upper-pos.md): basic property: positivity
- [Garwood upper bound after observing zero](garwood-upper-zero.md): special case: the bound after observing zero
- [Garwood upper bound is strictly increasing in the count](garwood-upper-strict-mono.md): basic property: increasing in the count
- [Means below the Garwood upper bound are exactly the non-rejected ones](le-garwood-upper-iff.md): lemma used in the proof of the main statement
- [Super-uniformity of the distribution-function transform](poisson-measure-real-poisson-cdf-le.md): lemma used in the proof of the main statement

## Background

- [Poisson–Gamma duality](../poisson-gamma-duality-identity/README.md)

## Sources

- F. Garwood, "Fiducial limits for the Poisson distribution", *Biometrika* (1936).
