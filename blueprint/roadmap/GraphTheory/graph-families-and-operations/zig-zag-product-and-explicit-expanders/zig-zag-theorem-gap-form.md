# Zig-zag theorem, spectral-gap form

Let $V$, $K$ and $L$ be finite sets, $G$ a [rotation map](rotation-map.md) on $V \times K$ describing an $(N_1, D_1, \lambda_1)$-graph and $H$ a rotation map on $K \times L$ describing a $(D_1, D_2, \lambda_2)$-graph with $\lambda_2 \le 1$. Then the [zig-zag product](zigzag.md) has spectral gap at least the product of the gap of $G$ and the square of the gap of $H$: it is an

$$\big(N_1 D_1,\ D_2^2,\ 1 - (1 - \lambda_1)(1 - \lambda_2)^2\big)\text{-graph};$$

in particular $\lambda \le \lambda_1 + 2\lambda_2$, and $\lambda < 1$ when $\lambda_1, \lambda_2 < 1$ (S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7 (2012), Theorem 4.35, with $\gamma_i = 1 - \lambda_i$, where spectral gaps lie in $[0, 1]$; the source's restriction $\lambda_1 \le 1$ is not needed for the bound; compare O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Theorem 3.2, $f(\lambda_1, \lambda_2) < 1$ when $\lambda_1, \lambda_2 < 1$).

The proof is Vadhan's matrix decomposition $\tilde B = (1 - \lambda_2)\tilde J + \lambda_2 \tilde E$ applied to the vector: with the notation of the [zig-zag theorem](zig-zag-theorem.md), $\tilde B x = (1 - \lambda_2) x^\parallel + f$ where $f = \lambda_2 x^\parallel + \tilde B x^\perp$ has $\lVert f\rVert \le \lambda_2 \lVert x\rVert$ because $x^\parallel \perp \tilde B x^\perp$; expanding $\langle \tilde A \tilde B x, \tilde B x\rangle$ bounds the quadratic form by $(1 - \lambda_2)^2 \lambda_1 + 2(1 - \lambda_2)\lambda_2 + \lambda_2^2 = 1 - (1 - \lambda_1)(1 - \lambda_2)^2$. Like the [zig-zag theorem](zig-zag-theorem.md), this is weaker than the improved bound of Reingold, Vadhan and Wigderson, Theorem 4.3.

## Background

- [Zig-zag theorem](zig-zag-theorem.md): the original bound $\lambda_1 + \lambda_2 + \lambda_2^2$; neither bound
  implies the other for all parameters.
