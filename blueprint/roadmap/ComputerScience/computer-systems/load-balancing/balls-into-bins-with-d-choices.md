# Balls into bins with d choices

In an $(m, n, d)$-problem, $m$ balls are placed sequentially into $n$ initially empty bins; for each ball, $d$ bins are chosen independently and uniformly at random, with replacement. The *greedy* algorithm places each ball in the least loaded of its $d$ chosen bins, breaking ties arbitrarily. The load of a bin is the number of balls in it, and the *maximum load* is the largest load at the end. For $d = 1$ this is throwing each ball into one uniform bin, whose maximum load for $m = n$ is the [maximum load of balls into bins](../../randomized-algorithms/maximum-load-of-balls-into-bins.md).

## Depends on

- [Maximum load of balls into bins](../../randomized-algorithms/maximum-load-of-balls-into-bins.md)

## Sources

- M. Mitzenmacher, *The Power of Two Choices in Randomized Load Balancing*, PhD thesis, University of California, Berkeley, 1996, <https://www.eecs.harvard.edu/~michaelm/postscripts/mythesis.pdf>, Section 1.2 (the $(m, n, d)$-problem and the greedy algorithm).
- Y. Azar, A. Z. Broder, A. R. Karlin and E. Upfal, "Balanced allocations", *SIAM Journal on Computing* 29(1):180–200, 1999.
