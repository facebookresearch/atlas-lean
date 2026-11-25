# No element growth in Cholesky factorization

Let $L$ and $A$ be real square matrices indexed by a finite set, with $A = L L^T$. Then for all indices $i, j$

$$(|L|\,|L^T|)_{ij} = \sum_k |L_{ik}|\,|L_{jk}| \le \sqrt{A_{ii}}\,\sqrt{A_{jj}},$$

by the Cauchy–Schwarz inequality, since $A_{ii} = \sum_k L_{ik}^2$ (J. W. Demmel, Math 221, UC Berkeley, Lecture 6 notes, 2024). The backward error of Cholesky factorization is bounded by a multiple of $n u\,|L|\,|L^T|$, as for LU, so this shows that Cholesky is backward stable without any pivoting: the factor $|L|\,|L^T|$ is at most the largest diagonal entry of $A$.

## Background

- [Backward error of floating-point LU factorization](exists-mul-eq-add-abs-le-gamma.md): the corresponding statement for Gaussian elimination, where $|\hat L|\,|\hat U|$ must be controlled by pivoting.
