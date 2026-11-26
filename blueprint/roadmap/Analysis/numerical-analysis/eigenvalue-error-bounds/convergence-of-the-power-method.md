# Convergence of the power method

Let $A$ be an $n \times n$ complex matrix with exactly one eigenvalue $\lambda_1$ of largest modulus, and suppose that $\lambda_1$ is semisimple, that is, its algebraic and geometric multiplicities agree. Let $P_1$ be the spectral projector of $A$ onto the generalized eigenspace of $\lambda_1$ along the other generalized eigenspaces, and let $v_0$ be a vector with $P_1 v_0 \ne 0$. Then the directions of the power iterates $A^k v_0$ converge to the direction of the eigenvector $P_1 v_0$:

$$\frac{A^k v_0}{\lambda_1^k} \to P_1 v_0 \quad (k \to \infty), \qquad \text{hence} \qquad \frac{(A^k v_0)^* A\, A^k v_0}{(A^k v_0)^* A^k v_0} \to \lambda_1 .$$

The convergence is linear, with the ratio $|\lambda_2|/|\lambda_1|$ of the second largest to the largest eigenvalue modulus governing the rate.

## Expansion

This node states a precise result. A good expansion adds pages for:

- Statement prerequisite: the spectral projectors $P_i$ of a square matrix onto its generalized eigenspaces, with $\sum_i P_i = I$ and $A P_i = P_i(\lambda_i P_i + D_i)$, $D_i$ nilpotent.
- The convergence of the normalized iterates $v_k = A v_{k-1}/\alpha_k$ of the cited Algorithm 4.1, where $\alpha_k$ is a component of $A v_{k-1}$ of largest modulus. The cited theorem asserts that $v_k$ converges to an eigenvector and $\alpha_k \to \lambda_1$; that form needs a rule for choosing among components of equal modulus, since for a limit direction such as $(1, -1)$ the choice can alternate between the two components and $v_k$ then alternates in sign. The expansion should state that form with an explicit tie-breaking hypothesis.
- The rate: $\|A^k v_0/\lambda_1^k - P_1 v_0\| = O(k^{m} (|\lambda_2|/|\lambda_1|)^k)$, where $m$ is one less than the largest size of a Jordan block of an eigenvalue of modulus $|\lambda_2|$.

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 4.1.1, Algorithm 4.1, Theorem 4.1 and its proof, equation (4.2), and the convergence factor $\rho_D = |\lambda_2|/|\lambda_1|$ stated after it. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
