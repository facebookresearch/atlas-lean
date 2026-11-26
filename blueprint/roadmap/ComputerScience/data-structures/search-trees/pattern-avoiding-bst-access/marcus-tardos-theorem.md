# Marcus–Tardos theorem on excluded permutation matrices

For every $k \times k$ permutation matrix $P$ there is a constant $c_P$ such that every $n \times n$ $0$-$1$ matrix that does not contain $P$ as a submatrix (after deleting rows and columns and turning some ones into zeros) has at most $c_P\, n$ ones. Equivalently, the Füredi–Hajnal conjecture holds, and it implies the Stanley–Wilf conjecture that the number of $\pi$-avoiding permutations of $[n]$ is at most $C_\pi^n$.

## Proof sketch

Partition the matrix into $(n/k^2) \times (n/k^2)$ blocks of size $k^2 \times k^2$. A block is *wide* if it has ones in at least $k$ columns and *tall* if it has ones in at least $k$ rows; a block row containing $k\binom{k^2}{k}$ or more wide blocks would yield a copy of $P$ by the pigeonhole principle, so each block row has fewer than $k\binom{k^2}{k}$ wide blocks, a constant, and likewise each block column has fewer than $k\binom{k^2}{k}$ tall blocks; over all $n/k^2$ block rows and columns there are $O(n/k^2)$ wide and tall blocks in total. Applying induction to the contracted $(n/k^2)\times(n/k^2)$ matrix of nonzero blocks gives the recurrence $f(n) \le (k-1)^2 f(n/k^2) + O(n)$, hence $f(n) = O(n)$.

## Depends on

- [Pattern-avoiding access sequences](pattern-avoiding-access-sequence.md)

## Sources

- Adam Marcus, Gábor Tardos, "Excluded Permutation Matrices and the Stanley–Wilf Conjecture", Journal of Combinatorial Theory, Series A 107(1) (2004).
