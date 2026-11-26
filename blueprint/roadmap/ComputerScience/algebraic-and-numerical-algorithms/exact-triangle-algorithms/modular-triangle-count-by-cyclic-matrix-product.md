# Counting modular zero triangles by matrix multiplication over a cyclic ring

For a prime $p$ define matrices over the ring $\mathbb{Z}[x]/(x^p - 1)$ by $P_{ij} = x^{A_{ij} \bmod p}$ and $Q_{jk} = x^{B_{jk} \bmod p}$. Then for every pair $(i, k)$ the coefficient of $x^{(-C_{ik}) \bmod p}$ in $(PQ)_{ik}$ equals the number of $j$ with $A_{ij} + B_{jk} + C_{ik} \equiv 0 \pmod p$, so $Z_p$ is a sum of $n^2$ selected coefficients of $PQ$. The product $PQ$ can be computed by Strassen's seven-product recursion over this ring with $O(n^{\log_2 7})$ ring operations, each a cyclic convolution of length $p$, and every coefficient stays in $[0, n]$.

## Proof sketch

Multiplying monomials adds exponents modulo $p$; the coefficient extraction counts middle vertices. Strassen's identities hold over every commutative ring.

## Depends on

- [Modular triangle counts and false positives](modular-triangle-counts.md)
- [Strassen's matrix accumulator](../strassen-algorithm/strassen-matrix-accumulate.md)

## Proof depends on

- [Correctness of Strassen's matrix accumulator](../strassen-algorithm/strassen-matrix-accumulate-ret.md)

## Sources

- V. Strassen, "Gaussian Elimination is not Optimal", Numerische Mathematik 13, 1969.
- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", arXiv:2610.06783, 2026.
