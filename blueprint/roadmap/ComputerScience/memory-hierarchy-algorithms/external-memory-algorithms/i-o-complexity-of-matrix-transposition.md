# I/O complexity of matrix transposition

In the single-disk [external-memory model](the-external-memory-model.md) with internal memory of $M$ records and blocks of $B$ records, the number of I/Os required to transpose a $p \times q$ matrix stored in row-major order, with $N = pq$ records and $p, q \ge 2$, provided the pass factor $\log \min\{M, 1 + \min\{p, q\}, 1 + N/B\} / \log(1 + M/B)$ is at least $1$, is

$$
\Theta\left( \frac{N}{B} \cdot \frac{\log \min\{M,\ 1 + \min\{p, q\},\ 1 + N/B\}}{\log(1 + M/B)} \right).
$$

When $B$ is large, transposition is as hard as sorting; for smaller $B$ the special structure of the transposition permutation makes it easier. The proviso matters: the expression counts passes over the file, and below one pass it undercounts. For $B = 1$ the factor is below $1$, while a transposition with $p, q \ge 2$ moves at least $N/2$ records (the permutation, $k \mapsto kp \bmod (N - 1)$ for $k < N - 1$ with $N - 1$ fixed, has $\gcd(p - 1, q - 1) + 1 \le \min\{p, q\} \le N/2$ fixed points), each of which must be read, so at least $N/(2B)$ I/Os are needed. For $p = 1$ or $q = 1$ the transposition leaves the row-major order unchanged and needs no I/O.

## Depends on

- [The external-memory model](the-external-memory-model.md)

## Sources

- A. Aggarwal and J. S. Vitter, "The input/output complexity of sorting and related problems", *Communications of the ACM* 31(9):1116–1127, 1988, Section 3, Theorem 3.3 (bound (3.5)) with $P = 1$ and the remark following it.
