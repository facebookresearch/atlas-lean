# LU decomposition

Let $K$ be a field and $A$ an $n \times n$ matrix over $K$ whose leading principal minors are all nonzero: for every $k \le n$, the upper-left $k \times k$ block has nonzero determinant. Then $A = LU$ with $L$ lower triangular with every diagonal entry $1$ and $U$ upper triangular.

## Idea

Gaussian elimination without row exchanges subtracts multiples of each pivot row from the rows below it. The multipliers form the unit lower-triangular matrix $L$, and what remains is the upper-triangular $U$. Elimination succeeds exactly when every pivot is nonzero, and the $k$-th pivot is the ratio of the $k$-th and $(k-1)$-th leading principal minors, which explains the hypothesis. For an invertible matrix the factorization is unique. Once $A = LU$ is known, each system $Ax = b$ is solved by two triangular substitutions; in general a row permutation is needed first, giving $PA = LU$.

## Statements

- [LU decomposition without pivoting](exists-lu-decomposition-of-minors-ne-zer.md)
- [Uniqueness of the LU decomposition](lu-decomposition-unique.md): uniqueness for invertible matrices

## Related topics

- [Rounding error analysis](../../../ComputerScience/algebraic-and-numerical-algorithms/rounding-error-analysis/README.md): the factors computed in floating point are the exact factors of $A + E$ with $|E| \le \gamma_n |\hat L|\,|\hat U|$.
- [Condition number bound for linear systems](../perturbation-theory-for-linear-systems/condition-number-bound/norm-sub-div-norm-le.md): how such a backward error turns into an error bound for the solution of $Ax = b$.
