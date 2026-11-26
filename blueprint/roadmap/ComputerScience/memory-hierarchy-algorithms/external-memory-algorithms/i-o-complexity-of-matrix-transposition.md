# I/O complexity of matrix transposition

In the single-disk [external-memory model](the-external-memory-model.md) with internal memory of $M$ records and blocks of $B$ records, the number of I/Os required to transpose a $p \times q$ matrix stored in row-major order, with $N = pq$ records, is

$$
\Theta\left( \frac{N}{B} \cdot \frac{\log \min\{M,\ 1 + \min\{p, q\},\ 1 + N/B\}}{\log(1 + M/B)} \right).
$$

When $B$ is large, transposition is as hard as sorting; for smaller $B$ the special structure of the transposition permutation makes it easier.

## Depends on

- [The external-memory model](the-external-memory-model.md)

## Sources

- A. Aggarwal and J. S. Vitter, "The input/output complexity of sorting and related problems", *Communications of the ACM* 31(9):1116–1127, 1988, Section 3, Theorem 3.3 (bound (3.5)) with $P = 1$ and the remark following it.
