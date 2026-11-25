# Convergence in W_p is weak convergence with convergence of p-th moments

Let $X$ be a Polish metric space, $p \in [1, \infty)$ and $x_0 \in X$, and let $\mu_k$ and $\mu$ be
Borel probability measures with finite $p$-th moments. Then $W_p(\mu_k, \mu) \to 0$ if and only if
$\mu_k \to \mu$ weakly, against bounded continuous functions, and
$\int d(x_0, x)^p \, d\mu_k(x) \to \int d(x_0, x)^p \, d\mu(x)$.

## Idea

Weak convergence alone lets a small amount of mass escape far away, which $W_p$ notices: the
measures $(1 - 1/k)\delta_0 + (1/k)\delta_k$ on the real line converge weakly to $\delta_0$, but
their $W_1$ distance to it is always $1$. Convergence of the $p$-th moments rules this out, and the
theorem says that nothing else separates the two notions. One direction is short: for a bounded
$L$-Lipschitz $f$, $|\int f \, d\mu_k - \int f \, d\mu| \le L\, W_1(\mu_k, \mu) \le L\, W_p(\mu_k, \mu)$,
and bounded Lipschitz functions determine weak convergence.

## Statements

- [Convergence in $W_p$ is weak convergence with convergence of $p$-th moments](tendsto-wasserstein-iff.md)
- [Convergence in Wasserstein distance implies weak convergence](tendsto-of-tendsto-wasserstein.md): one direction.

## Background

- [Wasserstein distance](../wasserstein-distance/README.md): the distance of the statement.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer, 2009, Chapter 6.
