# Quantile function

Let $\mu$ be a measure on $\mathbb{R}$ with cumulative distribution function $F_\mu$ (for a probability measure, $F_\mu(x) = \mu((-\infty, x])$). The quantile function of $\mu$, the generalised inverse of $F_\mu$, is the function $Q_\mu : \mathbb{R} \to \mathbb{R}$ given by $Q_\mu(u) = \inf \lbrace x \in \mathbb{R} : u \le F_\mu(x) \rbrace$ for $u \in (0, 1)$ and $Q_\mu(u) = 0$ for $u \notin (0, 1)$.

## Idea

$Q_\mu(u)$ is the smallest point at which the distribution function reaches the level $u$; when $F_\mu$ is continuous and strictly increasing it is the inverse function $F_\mu^{-1}$. The infimum handles jumps and flat stretches of $F_\mu$ and gives the rule $Q_\mu(u) \le x$ if and only if $u \le F_\mu(x)$, for $u \in (0, 1)$. The quantile function is measurable and nondecreasing on $(0, 1)$, though not on all of $\mathbb{R}$ because of the convention outside $(0, 1)$ (for the point mass at $2$, $Q(1/2) = 2 > 0 = Q(1)$); for a probability measure, $Q_\mu(1/2)$ is a median.

## Statements

- [Quantile function of a real measure](cdf-quantile.md)
- [The quantile function as a generalized inverse of the cdf](cdf-quantile-le-iff.md): basic property: generalised inverse of the distribution function on $(0, 1)$
- [The cdf at the quantile is at least the level](cdf-quantile-mem.md): basic property on $(0, 1)$
- [Monotonicity of the quantile function](cdf-quantile-mono-on.md): basic property: nondecreasing on $(0, 1)$
- [Measurability of the quantile function](measurable-cdf-quantile.md): basic property: measurability

## Background

- [Atoms and continuity points of a distribution function](../../cumulative-distribution-function/README.md)
