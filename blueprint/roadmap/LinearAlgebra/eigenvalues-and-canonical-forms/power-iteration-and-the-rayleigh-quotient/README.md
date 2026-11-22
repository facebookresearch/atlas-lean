# Power iteration

Let $T$ be a linear operator on a finite-dimensional real inner product space with an orthonormal eigenbasis $(b_j)$, $T b_j = \lambda_j b_j$. Let $q = b_{i_0}$ with $\lambda_{i_0} \ne 0$, let $\mu \ge 0$ bound $|\lambda_j|$ for $j \ne i_0$, put $\rho = \mu / |\lambda_{i_0}|$, and let $v_0$ have $c = \langle q, v_0 \rangle \ne 0$. Then the power iterates $v_k = T^k v_0 / \|T^k v_0\|$ satisfy $\|v_k - s_k q\| \le 2\rho^k \|v_0\| / |c|$ for some signs $s_k = \pm 1$.

## Idea

Power iteration repeatedly applies $T$ and normalizes. In the eigenbasis, $T^k v_0 = \sum_j \lambda_j^k \langle b_j, v_0 \rangle b_j$, and the dominant term grows fastest, so after normalization the iterate lines up with the dominant eigenvector $q$, up to sign, at the linear rate $\rho = |\lambda_2/\lambda_1|$ when $\lambda_{i_0}$ is strictly dominant. The Rayleigh quotient $\langle v, Tv \rangle / \|v\|^2$ of the iterate estimates the eigenvalue with error of order $\rho^{2k}$, because for a symmetric operator it is quadratically accurate near an eigenvector. Inverse iteration, Rayleigh quotient iteration and the QR algorithm refine this idea.

## Statements

- [Power iteration converges to the dominant eigenvector up to sign](exists-sign-norm-normalize-sub-le.md)
- [Power iteration converges linearly (unnormalized form)](norm-smul-pow-apply-sub-le.md): the unnormalized bound
- [The power-iteration eigenvalue estimate converges twice as fast](abs-rayleigh-pow-apply-sub-le.md): the eigenvalue estimate converges at the squared rate
- [Quadratic accuracy of the Rayleigh quotient](inner-apply-sub-eq-of-eigen.md): the Rayleigh quotient is quadratically accurate
- [Coordinates of powers in an eigenbasis](inner-pow-apply.md): coordinates of $T^k v$ in the eigenbasis
- [Powers of an operator on an eigenvector](pow-apply-of-eigen.md): powers of $T$ on an eigenvector
- [Normalizing at most doubles the distance to a unit vector](norm-normalize-sub-le.md): normalizing at most doubles the distance to a unit vector

## Background

- [Diagonalization](../diagonalization/README.md): the statements assume an eigenbasis, and the convergence argument expands the iterates in it.

## Related topics

- [The Arnoldi relation](../../matrix-decompositions/arnoldi-and-lanczos-iterations/arnoldi-relation.md): Krylov methods keep all the vectors $v_0, Tv_0, \dots, T^{k-1} v_0$, of which power iteration keeps only the last, and orthonormalize them.
- [Principal component analysis](../../../Probability/linear-models-multivariate/principal-component-analysis/README.md)
