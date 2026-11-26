# Convergence of the power method

Let $A$ be an $n \times n$ complex matrix with exactly one eigenvalue $\lambda_1$ of largest modulus, and suppose that $\lambda_1$ is semisimple, that is, its algebraic and geometric multiplicities agree. Let $P_1$ be the spectral projector of $A$ onto the generalized eigenspace of $\lambda_1$ along the other generalized eigenspaces, and let $v_0$ be a vector with $P_1 v_0 \ne 0$. Then the directions of the power iterates $A^k v_0$ converge to the direction of the eigenvector $P_1 v_0$:

$$\frac{A^k v_0}{\lambda_1^k} \to P_1 v_0 \quad (k \to \infty), \qquad \text{hence} \qquad \frac{(A^k v_0)^* A\, A^k v_0}{(A^k v_0)^* A^k v_0} \to \lambda_1 .$$

The convergence is linear, with the ratio $|\lambda_2|/|\lambda_1|$ of the second largest to the largest eigenvalue modulus governing the rate. For a real symmetric matrix, with an orthonormal eigenbasis, the rate is [Power iteration converges linearly (unnormalized form)](../../../LinearAlgebra/eigenvalues-and-canonical-forms/power-iteration-and-the-rayleigh-quotient/norm-smul-pow-apply-sub-le.md), and the normalized iterates converge up to sign by [Power iteration converges to the dominant eigenvector up to sign](../../../LinearAlgebra/eigenvalues-and-canonical-forms/power-iteration-and-the-rayleigh-quotient/exists-sign-norm-normalize-sub-le.md).

## Depends on

- [Spectral projectors of a square matrix](spectral-projectors.md)

## Proof depends on

- [Rate of convergence of the power iterates](power-iterates-converge-at-the-rate-of-the-subdominant-eigenvalues.md)

## Related topics

- [Convergence of the power method with max-component normalization](normalized-power-method-converges.md): the normalized iteration of the cited algorithm.

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 4.1.1, Algorithm 4.1, Theorem 4.1 and its proof, equation (4.2), and the convergence factor $\rho_D = |\lambda_2|/|\lambda_1|$ stated after it. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
