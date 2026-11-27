# Multidimensional Itô formula and covariation

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space, $B=(B^1,\ldots,B^m)$ an $m$-dimensional $(\mathcal F_t)$-[Brownian motion](../construction-and-sample-paths-of-brownian-motion/multidimensional-brownian-motion.md), and $X=(X^1,\ldots,X^d)$ a $d$-dimensional Itô process

$$X^i_t=X^i_0+\int_0^tb^i_s\,ds+\sum_{k=1}^m\int_0^t\sigma^{ik}_s\,dB^k_s,\qquad i=1,\ldots,d,$$

with progressively measurable $b^i$ and $\sigma^{ik}$ satisfying $\int_0^t|b^i_s|\,ds<\infty$ and $\int_0^t(\sigma^{ik}_s)^2\,ds<\infty$ almost surely for every $t$. Then:

1. **Covariation.** For all $i,j$ and $t$, the sums $\sum_k(X^i_{t_{k+1}}-X^i_{t_k})(X^j_{t_{k+1}}-X^j_{t_k})$ over partitions of $[0,t]$ with mesh tending to $0$ converge in probability to

    $$[X^i,X^j]_t=\int_0^t(\sigma_s\sigma_s^{\mathsf T})_{ij}\,ds .$$

2. **Itô's formula.** For every $f\in C^2(\mathbb R^d)$, almost surely for all $t\ge0$,

    $$f(X_t)=f(X_0)+\sum_{i=1}^d\int_0^t\partial_if(X_s)\,dX^i_s+\frac12\sum_{i,j=1}^d\int_0^t\partial_{ij}f(X_s)\,d[X^i,X^j]_s,$$

    where $\int\partial_if(X)\,dX^i=\int\partial_if(X)b^i\,ds+\sum_k\int\partial_if(X)\sigma^{ik}\,dB^k$.

Example: if $X$ takes values in the simplex and $\sigma\sigma^{\mathsf T}(X_s)=\bigl(X^i_s(\delta_{ij}-X^j_s)\bigr)_{ij}$, as for the [K-allele Wright–Fisher diffusion](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md), then $d[X^i,X^j]_t=X^i_t(\delta_{ij}-X^j_t)\,dt$ and the second-order term of the formula is the diffusion part of that generator.

## Depends on

- [Multidimensional Brownian motion](../construction-and-sample-paths-of-brownian-motion/multidimensional-brownian-motion.md)
- [Itô processes and their quadratic variation](ito-processes-and-their-quadratic-variation.md)

## Proof depends on

- [Itô's formula for Itô processes with locally integrable coefficients](ito-formula-for-ito-processes-time-dependent-loc.md)

## Expansion

A full proof page must establish the following.

- Item 1 by polarization, $[X^i,X^j]=\frac14\bigl([X^i+X^j]-[X^i-X^j]\bigr)$, from the one-dimensional quadratic variation of Itô processes, together with $[B^k,B^l]_t=\delta_{kl}t$ for independent coordinates.
- Item 2 by the multivariate second-order Taylor expansion along partitions, after the same localization and truncation steps as in the [one-dimensional localized formula](ito-formula-for-ito-processes-time-dependent-loc.md).
- The simplex example.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, multidimensional Itô rule (statement and proof).
