# Powers of a matrix tend to zero exactly when its spectral radius is less than one

Let $A$ be an $n \times n$ complex matrix with spectral radius $\rho(A) = \max\{|\lambda| : \lambda \text{ an eigenvalue of } A\}$. Then $A^k \to 0$ as $k \to \infty$ if and only if $\rho(A) < 1$.

If $Au = \lambda u$ with $\|u\|_2 = 1$ and $|\lambda| = \rho(A)$, then $|\lambda|^k = \|A^k u\|_2$, which tends to $0$ when $A^k \to 0$. Conversely, writing $A = XJX^{-1}$ in Jordan form, each Jordan block $J_i = \lambda_i I + N_i$ with $N_i$ nilpotent of index $l_i$ has $J_i^k = \sum_{j < l_i} \binom{k}{j} \lambda_i^{k-j} N_i^j$, which tends to $0$ when $|\lambda_i| < 1$.

## Proof depends on

- [Jordan normal form](../../../LinearAlgebra/eigenvalues-and-canonical-forms/jordan-normal-form/exists-jordan-normal-form-of-splits.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 1.8.4, Theorem 1.10 and its proof. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
