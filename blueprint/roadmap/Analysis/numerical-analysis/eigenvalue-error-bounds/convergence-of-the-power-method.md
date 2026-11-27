# Convergence of the power method

Let $A$ be an $n \times n$ complex matrix with exactly one eigenvalue $\lambda_1$ of largest modulus, suppose that $\lambda_1 \ne 0$ (that is, $A$ is not nilpotent) and that $\lambda_1$ is semisimple, that is, its algebraic and geometric multiplicities agree. Let $P_1$ be the spectral projector of $A$ onto the generalized eigenspace of $\lambda_1$ along the other generalized eigenspaces, and let $v_0$ be a vector with $P_1 v_0 \ne 0$. Then the directions of the power iterates $A^k v_0$ converge to the direction of the eigenvector $P_1 v_0$:

$$\frac{A^k v_0}{\lambda_1^k} \to P_1 v_0 \quad (k \to \infty), \qquad \text{hence} \qquad \frac{(A^k v_0)^* A\, A^k v_0}{(A^k v_0)^* A^k v_0} \to \lambda_1 .$$

When $A$ has another eigenvalue, the error $\|A^k v_0/\lambda_1^k - P_1 v_0\|$ is at most a polynomial in $k$ times $(|\lambda_2|/|\lambda_1|)^k$, where $|\lambda_2|$ is the largest modulus of the other eigenvalues; when $\lambda_1$ is the only eigenvalue, $A^k v_0/\lambda_1^k = P_1 v_0 = v_0$ for every $k$. For a real symmetric matrix, with an orthonormal eigenbasis, the rate is [Power iteration converges linearly (unnormalized form)](../../../LinearAlgebra/eigenvalues-and-canonical-forms/power-iteration-and-the-rayleigh-quotient/norm-smul-pow-apply-sub-le.md), and the normalized iterates converge up to sign by [Power iteration converges to the dominant eigenvector up to sign](../../../LinearAlgebra/eigenvalues-and-canonical-forms/power-iteration-and-the-rayleigh-quotient/exists-sign-norm-normalize-sub-le.md).

## Related topics

- [Power iteration converges linearly (unnormalized form)](../../../LinearAlgebra/eigenvalues-and-canonical-forms/power-iteration-and-the-rayleigh-quotient/norm-smul-pow-apply-sub-le.md)
- [Power iteration converges to the dominant eigenvector up to sign](../../../LinearAlgebra/eigenvalues-and-canonical-forms/power-iteration-and-the-rayleigh-quotient/exists-sign-norm-normalize-sub-le.md)

## Expansion

This node states a precise result. A good expansion adds pages for:

- Statement prerequisite: the spectral projectors $P_i$ of a square matrix onto its generalized eigenspaces, with $\sum_i P_i = I$ and $A P_i = P_i(\lambda_i P_i + D_i)$, $D_i$ nilpotent.
- The convergence of the normalized iterates $v_k = A v_{k-1}/\alpha_k$ of the cited Algorithm 4.1, where $\alpha_k$ is a component of $A v_{k-1}$ of largest modulus. A rule for breaking ties does not suffice: for $A$ with $Aq = q$ and $Aw = -w/2$, $q = (1, -1)$, $w = (1, 1)$ and $v_0 = q + w$, the component of largest modulus of $A^k v_0 = (1 + t, -1 + t)$, $t = (-1/2)^k$, is unique but alternates, and $v_k$ has subsequences tending to $q$ and to $-q$. The expansion should state that form under the hypothesis that $P_1 v_0$ has exactly one component of largest modulus.
- The rate in the non-normal case: $\|A^k v_0/\lambda_1^k - P_1 v_0\| = O(k^{m} (|\lambda_2|/|\lambda_1|)^k)$, where $m$ is one less than the largest size of a Jordan block of an eigenvalue of modulus $|\lambda_2|$; the symmetric case is already stated in the power iteration pages linked above.

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 4.1.1, Algorithm 4.1, Theorem 4.1 and its proof, equation (4.2), and the convergence factor $\rho_D = |\lambda_2|/|\lambda_1|$ stated after it. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
