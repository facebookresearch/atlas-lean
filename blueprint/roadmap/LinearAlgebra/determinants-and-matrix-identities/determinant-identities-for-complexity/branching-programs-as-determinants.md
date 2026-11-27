# Algebraic branching programs as determinants

Let $N$ be the weighted adjacency matrix of a DAG on vertices $0,\dots,m$ in topological order ($N_{ij}=0$ unless $i<j$). Then the total weight $q_j$ of all paths from $0$ to $j$ satisfies $q=e_0+qN$, so $q=e_0(I-N)^{-1}$; since $I-N$ is unitriangular with determinant $1$, its inverse is its adjugate, and the value $q_m$ of the branching program equals $(-1)^{m}$ times the determinant of the $m\times m$ submatrix of $I-N$ obtained by deleting row $m$ and column $0$. Hence every algebraic branching program with $m+1$ vertices and affine-linear edge labels computes an affine projection of the $m\times m$ determinant: after multiplying one row of that submatrix by $-1$ when $m$ is odd, its value is $\det M$ for an $m\times m$ matrix $M$ with affine-linear entries, a determinantal representation of size $m$.

## Proof sketch

Solve the triangular system $q(I-N)=e_0$; Cramer's rule gives $q_m=\operatorname{adj}(I-N)_{0m}$, a signed minor.

## Depends on

- [Leibniz formula for the determinant](../determinants-of-matrices/leibniz-formula/det-apply.md)
- [Specialization matrices and determinantal representations](../../../TheoryOfComputation/algebraic-complexity/determinantal-and-permanental-complexity/specialization-matrices-and-determinantal-representations.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Ramprasad Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", 2026.
