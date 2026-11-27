# A sharper comparison bound for merge sort

Merging two sorted lists of lengths $p, q \ge 1$ with any comparison oracle uses at most $p + q - 1$ comparisons. Consequently top-down merge sort on $n$ elements uses at most $M(n)$ comparisons, where $M(0) = M(1) = 0$ and $M(n) = M(\lceil n/2 \rceil) + M(\lfloor n/2 \rfloor) + n - 1$, and $M(n) \le n \lceil \log_2 n \rceil - n + 1$ for $n \ge 1$. These bounds hold for arbitrary (even inconsistent) comparator answers, since only the number of queries is counted.

## Proof sketch

The last remaining element of a merge is placed without a comparison. The closed form follows by induction on $n$, using $\lceil \log_2 \lceil n/2 \rceil \rceil = \lceil \log_2 n \rceil - 1$ for $n \ge 2$.

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd ed., Addison-Wesley, 1998.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
