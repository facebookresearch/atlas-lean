# Marcus–Tardos theorem on excluded permutation matrices

For every $k \times k$ permutation matrix $P$ there is a constant $c_P$ such that every $n \times n$ $0$-$1$ matrix that does not contain $P$ (that is, has no $k \times k$ submatrix, obtained by deleting rows and columns, with a one wherever $P$ has one) has at most $c_P\, n$ ones. This proves the Füredi–Hajnal conjecture for permutation matrices, which by Klazar's reduction implies the Stanley–Wilf conjecture that the number of $\pi$-avoiding permutations of $[n]$ is at most $C_\pi^n$.

## Proof sketch

Let $f(n)$ be the maximum number of ones, and partition a $P$-avoiding matrix into $(n/k^2)^2$ blocks of size $k^2 \times k^2$. A block is *wide* if it has ones in at least $k$ columns and *tall* if it has ones in at least $k$ rows. A block column with $k\binom{k^2}{k}$ or more wide blocks would contain, by the pigeonhole principle, $k$ wide blocks with ones in the same $k$ columns, from which a copy of $P$ can be picked; so each block column has fewer than $k\binom{k^2}{k}$ wide blocks, and likewise each block row has fewer than $k\binom{k^2}{k}$ tall blocks. The matrix of nonzero blocks also avoids $P$, and a block that is neither wide nor tall has at most $(k-1)^2$ ones, so $f(n) \le (k-1)^2 f(n/k^2) + 2k^3\binom{k^2}{k}\, n$, hence $f(n) = O(n)$.

## Depends on

- [Classical pattern containment in a sequence](../../../../Combinatorics/permutations/permutation-patterns/cyclic-pattern-avoiding-stack-sorting/contains-pattern-seq.md)

## Sources

- Adam Marcus, Gábor Tardos, "Excluded Permutation Matrices and the Stanley–Wilf Conjecture", Journal of Combinatorial Theory, Series A 107(1) (2004).
