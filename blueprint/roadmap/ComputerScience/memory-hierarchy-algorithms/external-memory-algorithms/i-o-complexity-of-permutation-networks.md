# I/O complexity of permutation networks

A *permutation network* on $N$ inputs is a digraph of switch columns that can realize each of the $N!$ permutations of its inputs by setting its switches, the $i$-th node of each column holding the current contents of record $R_i$. In the single-disk [external-memory model](the-external-memory-model.md) with $N$ records, internal memory of $M$ records and blocks of $B$ records, computing any $N$-input permutation network requires

$$
\Omega\left( \frac{N}{B} \cdot \frac{\log(1 + N/B)}{\log(1 + M/B)} \right)
$$

I/Os in the average and worst case, and there are permutation networks that can be computed with $O\bigl((N/B)\log(1 + N/B)/\log(1 + M/B)\bigr)$ I/Os. Unlike general [permuting](i-o-complexity-of-permuting.md), the I/Os of a permutation network may not depend on the desired permutation, so the naive bound $N$ is not available.

## Depends on

- [The external-memory model](the-external-memory-model.md)

## Sources

- A. Aggarwal and J. S. Vitter, "The input/output complexity of sorting and related problems", *Communications of the ACM* 31(9):1116–1127, 1988, Section 2 (permutation networks) and Section 3, Theorem 3.1, bounds (3.2) and (3.3), with $P = 1$.
