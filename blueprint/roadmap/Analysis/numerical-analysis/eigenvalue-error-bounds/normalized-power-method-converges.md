# Convergence of the power method with max-component normalization

Let $A$ be an $n \times n$ complex matrix with exactly one eigenvalue $\lambda_1$ of largest modulus, and suppose that $\lambda_1 \ne 0$ and that $\lambda_1$ is semisimple. Let $P_1$ be its [spectral projector](spectral-projectors.md), let $v_0$ satisfy $P_1 v_0 \ne 0$, and suppose that the vector $P_1 v_0$ has exactly one component of largest modulus, the $j$-th. Define

$$v_k = \frac{1}{\alpha_k} A v_{k-1}, \qquad k \ge 1,$$

where $\alpha_k$ is a component of $A v_{k-1}$ of largest modulus (chosen by any rule when several components attain it). Then for all large $k$ the chosen component is the $j$-th, and

$$v_k \to \frac{P_1 v_0}{(P_1 v_0)_j}, \qquad \alpha_k \to \lambda_1 \qquad (k \to \infty);$$

the limit of $v_k$ is an eigenvector of $A$ for $\lambda_1$ with largest component $1$.

The uniqueness hypothesis on the largest component of $P_1 v_0$ is needed: for the $2 \times 2$ matrix with eigenvalues $1$ and $-1/2$ and eigenvectors $(1, -1)$ and $(1, 1)$, and $v_0 = (1, -1) + (1, 1)$, the component of largest modulus of $A v_{k-1}$ alternates between the two positions, and $v_k$ alternates between $(1, -1)$ and $(-1, 1)$ up to terms of order $2^{-k}$.

## Depends on

- [Spectral projectors of a square matrix](spectral-projectors.md)

## Proof depends on

- [Rate of convergence of the power iterates](power-iterates-converge-at-the-rate-of-the-subdominant-eigenvalues.md)

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 4.1.1, Algorithm 4.1 and Theorem 4.1 with its proof. The book's statement has no hypothesis on ties among the largest components of the limit; the uniqueness hypothesis is added here so that the normalized iterates converge. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
