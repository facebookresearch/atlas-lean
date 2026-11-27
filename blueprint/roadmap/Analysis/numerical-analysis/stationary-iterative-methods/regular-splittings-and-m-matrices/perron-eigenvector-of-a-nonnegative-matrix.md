# Perron eigenvector of a nonnegative matrix

Let $n \ge 1$ and let $B$ be a real $n \times n$ matrix with nonnegative entries, not necessarily irreducible. Then its spectral radius $\rho(B)$ is an eigenvalue of $B$, with an eigenvector $u \ne 0$ whose entries are all nonnegative.

This is the weak form of the Perron–Frobenius theorem; for irreducible $B$ the eigenvalue is simple and $u$ can be taken positive. It follows from the irreducible case applied to $B + \varepsilon E$, $E$ the all-ones matrix, and a limit as $\varepsilon \to 0$. The hypothesis $n \ge 1$ is needed: for $n = 0$ the only vector is $0$.

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)
- [Monotonicity of the spectral radius on nonnegative matrices](spectral-radius-is-monotone-on-nonnegative-matrices.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 1.10, Theorem 1.25 and the relaxed version for reducible matrices stated after it, as used in the proof of Theorem 1.29. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
