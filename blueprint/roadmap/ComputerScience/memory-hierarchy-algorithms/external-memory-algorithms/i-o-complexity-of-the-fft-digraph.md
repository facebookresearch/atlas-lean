# I/O complexity of the FFT digraph

In the single-disk [external-memory model](the-external-memory-model.md) with $N$ records, internal memory of $M$ records and blocks of $B$ records, the number of I/Os required, in the average case and the worst case, to compute the $N$-input FFT digraph, that is, to pebble all its nodes when a node may be pebbled only if its predecessors are pebbled and the records for them are in internal memory, is

$$
\Theta\left( \frac{N}{B} \cdot \frac{\log(1 + N/B)}{\log(1 + M/B)} \right),
$$

the same as for sorting.

## Depends on

- [The external-memory model](the-external-memory-model.md)

## Sources

- A. Aggarwal and J. S. Vitter, "The input/output complexity of sorting and related problems", *Communications of the ACM* 31(9):1116–1127, 1988, Section 2 (the FFT digraph and its pebbling) and Section 3, Theorem 3.1 with $P = 1$.
