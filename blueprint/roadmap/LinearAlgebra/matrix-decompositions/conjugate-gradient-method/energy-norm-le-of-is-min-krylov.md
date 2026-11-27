# The Chebyshev bound for Krylov energy minimizers

Let $A$ be a real symmetric positive definite $n \times n$ matrix whose eigenvalues all lie in
$[a, c]$ with $a > 0$, let $x^\star, x_0, x \in \mathbb{R}^n$ and $k \in \mathbb{N}$, and suppose that

$$\|x - x^\star\|_A \le \|x_0 + z - x^\star\|_A$$

for every $z$ in the [Krylov space](krylov.md) $\mathcal{K}_k\bigl(A, A(x^\star - x_0)\bigr)$. Then

$$\|x - x^\star\|_A \le 2 \left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^k
\|x_0 - x^\star\|_A, \qquad \kappa = c/a,$$

where $\|\cdot\|_A$ is the [energy norm](energy-norm.md). The vector $x$ is not required to lie in
$x_0 + \mathcal{K}_k(A, A(x^\star - x_0))$; when it does, the hypothesis says that it minimizes
$\|\cdot - x^\star\|_A$ there.

## Background

- [Minimax property of the Chebyshev polynomials](../../../Analysis/approximation-theory/minimax-property-of-the-chebyshev-polynomials/inv-two-pow-le-of-forall-abs-eval-le.md): the extremal property of $T_k$ behind the choice of the shifted and scaled Chebyshev polynomial; the residual polynomial of a Krylov method is normalized at $0$, which lies outside the spectral interval $[a, c]$.
- [The GMRES polynomial bound](../gmres/rss-le-of-is-gmresiterate.md): the same polynomial viewpoint for the residual of GMRES (Trefethen and Bau, Lectures 35 and 38).
