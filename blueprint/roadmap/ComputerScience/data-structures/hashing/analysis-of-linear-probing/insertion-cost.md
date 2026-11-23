# Expected cost of a linear-probing insertion

Let $N$ and $n$ be natural numbers. Consider all $N^{n+1}$ hash sequences
$a_1, \dots, a_{n+1}$ with values in the $N$ cells of a cyclic table, each equally likely. For
each of them, enter the first $n$ items by linear probing and count the [probes](probes.md) made
by the last one. The expected cost is the average of this count, a rational number; for $N = 0$
there are no hash sequences and the value is $0$, by the convention that division by zero gives
$0$.

For $n < N$ the table holding the first $n$ items is not full, and this is $M(N, n + 1)$ in
Knuth's 1963 note, the mean number of comparisons needed to place the $(n+1)$-th item. An
unsuccessful search for a key whose hash address is $a_{n+1}$ scans exactly the same cells (it
stops at the first empty cell), so it is also the expected cost of an unsuccessful search in a
table holding $n$ items. For $n \ge N \ge 1$ the first $n$ items fill the table, the last item
makes $N + 1$ probes by the full-table convention for [probes](probes.md), and the value is
$N + 1$.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Sections 1, 4 and 5: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
