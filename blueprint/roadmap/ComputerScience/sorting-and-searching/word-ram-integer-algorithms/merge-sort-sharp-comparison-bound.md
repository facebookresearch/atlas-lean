# A sharper comparison bound for merge sort

Merging two sorted lists of lengths $p, q \ge 1$ with any comparison oracle uses at most $p + q - 1$ comparisons. Consequently top-down merge sort on $n$ elements uses at most $M(n)$ comparisons, where $M(0) = M(1) = 0$ and $M(n) = M(\lceil n/2 \rceil) + M(\lfloor n/2 \rfloor) + n - 1$, and for $n \ge 1$

$$
M(n) = \sum_{k=1}^{n} \lceil \log_2 k \rceil = n \lceil \log_2 n \rceil - 2^{\lceil \log_2 n \rceil} + 1.
$$

These bounds hold for arbitrary (even inconsistent) comparator answers, since only the number of queries is counted.

## Proof sketch

The last remaining element of a merge is placed without a comparison. The sum form follows by induction on $n$, and grouping the $k$ with $2^{j-1} < k \le 2^j$ gives the closed form. Since $2^{\lceil \log_2 n \rceil} \ge n$, it implies the weaker bound $M(n) \le n \lceil \log_2 n \rceil - n + 1$, with equality exactly when $n$ is a power of $2$.

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd ed., Addison-Wesley, 1998.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
- P. Flajolet and M. Golin, "Mellin transforms and asymptotics: the mergesort recurrence", Acta Informatica 31, 1994: p. 675 (merge cost and the worst-case recurrence) and p. 678, Theorem 1 with its proof (the exact worst case $T(n) = \sum_{k=1}^{n} \lceil \lg k \rceil$). Author's copy: <https://algo.inria.fr/flajolet/Publications/FlGo94.pdf>
