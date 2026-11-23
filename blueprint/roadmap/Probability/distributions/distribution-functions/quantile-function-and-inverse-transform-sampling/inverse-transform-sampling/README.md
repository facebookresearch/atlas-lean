# Inverse transform sampling

Let $\mu$ be a probability measure on $\mathbb{R}$ with quantile function $Q_\mu$. The pushforward under
$Q_\mu$ of Lebesgue measure restricted to $[0, 1]$ is $\mu$.

## Idea

Every law on the line can be simulated from uniform random numbers: if $U$ is uniform on $[0, 1]$,
then $Q_\mu(U)$ has law $\mu$. The reason is the rule $Q_\mu(u) \le x$ if and only if $u \le F_\mu(x)$,
valid for $u \in (0, 1)$: it gives $P(Q_\mu(U) \le x) = P(U \le F_\mu(x)) = F_\mu(x)$, and a law on the
line is determined by its distribution function. For the exponential law with rate $\lambda > 0$,
$Q(u) = -\log(1 - u)/\lambda$ for $0 < u < 1$, so $-\log(1 - U)/\lambda$ is exponentially distributed, $U$
avoiding the endpoints almost surely.

## Statements

- [Inverse transform sampling](map-cdf-quantile-restrict-icc.md)

## Background

- [Quantile function](../quantile-function/README.md): the quantile function and its rule $Q_\mu(u) \le x \iff u \le F_\mu(x)$ for $0 < u < 1$
