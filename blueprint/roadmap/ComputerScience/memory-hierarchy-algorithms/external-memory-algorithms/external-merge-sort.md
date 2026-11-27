# External merge sort

In the [external-memory model](the-external-memory-model.md) with one disk, internal memory of $M$ records and blocks of $B$ records, where $B$, $M$ and $N$ are powers of $2$ with $B < M < N$ and $M \ge 4B$, the standard external merge sort sorts $N$ records with

$$
\frac{2N}{B}\left(1 + \left\lceil \log_{M/B - 1} \frac{N}{M} \right\rceil\right) = O\!\left(\frac{N}{B}\,\frac{\log(N/B)}{\log(M/B)}\right)
$$

I/Os. The run formation phase reads the input one memoryload at a time, sorts it internally and writes it back as one of $N/M$ sorted runs; each pass of the merging phase merges $M/B - 1$ runs into one, keeping one block of each run being merged and one output block in memory, and reads and writes every record once. This matches the lower bound of the model, so merge sort is an optimal external sorting algorithm.

## Depends on

- [The external-memory model](the-external-memory-model.md)

## Sources

- A. Aggarwal and J. S. Vitter, "The input/output complexity of sorting and related problems", *Communications of the ACM* 31(9):1116–1127, 1988, Section 5, "Merge Sort", equation (5.1), with $P = 1$ and $B$, $M$, $N$ powers of $2$ as assumed there. The condition $M \ge 4B$, which makes the logarithm base at least $3$, is added on this page.
