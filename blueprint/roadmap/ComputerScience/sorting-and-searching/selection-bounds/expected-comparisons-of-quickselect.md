# Expected comparisons of quickselect

Quickselect finds the element of rank $k$ among $n$ distinct keys by partitioning around a uniformly random pivot and recursing into the side that contains rank $k$. For every $n$ and every rank $k$ its expected number of comparisons is at most $4n$; for the median it is $(2 + 2\ln 2)n + o(n)$, the maximum over ranks to leading order.

## Depends on

- [Expected running time](../../randomized-algorithms/average-case-running-time/expected-time.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- D. E. Knuth, "Mathematical analysis of algorithms", *Information Processing 71*, North-Holland, 1972
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 4th ed., MIT Press, 2022
