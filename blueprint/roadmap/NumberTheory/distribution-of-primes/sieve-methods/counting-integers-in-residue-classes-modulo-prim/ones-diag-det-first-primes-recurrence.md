# Lemma 2, determinant recurrence

Let $p_1 < p_2 < \cdots$ be the primes in increasing
order. For $m \ge 0$ let $a_m$ be the determinant of the $m \times m$ integer matrix with
$p_1, \dots, p_m$ on the diagonal and $1$ in every other entry, and let $f_m = (-1)^m \det B_m$,
where $B_m$ is the $(m+1) \times (m+1)$ integer matrix whose first row consists of ones and
whose row $i + 1$, for $1 \le i \le m$, has $p_i$ in column $i$ and $1$ in every other column.
Then for every $k \ge 2$, $a_k = f_{k-1} + (p_k - 1) \cdot a_{k-1}$.

## Sources

- Florian Pausinger, "Counting Appearances of Integers in Sets of Arithmetic Progressions", Lemma 2.
