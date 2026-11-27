# Impagliazzo–Pudlák–Sgall: degree lower bound for subset sum

Over the field $\mathbb{R}$ of real numbers, let $n \ge 1$, let $c_1,\dots,c_n$ be nonzero reals and $m$ an arbitrary real. The polynomial $m - \sum_i c_i x_i$ together with the Boolean axioms has no PC refutation (and no Nullstellensatz refutation) of degree at most $\lceil n/2 \rceil$. When $m$ is not a subset sum of the $c_i$ the system is unsatisfiable and refutable in degree $n + 1$.

## Proof sketch

Apply the invariant method to the module of polynomials agreeing on the cube with $L \cdot r$ for $\deg r \le d - 1$, where $L = m - \sum c_i x_i$; a lemma bounding the degree of $L \cdot r$ from below by $\deg r + 1$ on the cube (valid while $\deg r < \lceil n/2\rceil$, proved from the full rank of the inclusion matrices between $k$-subsets and $(k+1)$-subsets of $[n]$ for $k < n/2$) shows that $1$ is not in the module.

## Depends on

- [Polynomial calculus proofs, degree and size](polynomial-calculus-proofs.md)
- [Nullstellensatz proofs and degree](nullstellensatz-proofs.md)

## Proof depends on

- [The invariant method for polynomial calculus degree lower bounds](invariant-method-for-pc-degree.md)
- [Polynomial calculus simulates Nullstellensatz, and conversely without bounds](polynomial-calculus-simulates-nullstellensatz.md)
- [Completeness of Nullstellensatz and PC over the Boolean cube](algebraic-proof-systems-completeness.md)

## Sources

- R. Impagliazzo, P. Pudlák and J. Sgall, "Lower Bounds for the Polynomial Calculus and the Gröbner Basis Algorithm", Computational Complexity 8(2), 127–144, 1999: Theorem 4.1 and Lemma 4.2 (Section 4, "A lower bound for subset sum over the reals").
