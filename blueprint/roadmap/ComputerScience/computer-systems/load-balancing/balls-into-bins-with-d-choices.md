# Balls into bins with d choices

In an $(m, n, d)$-problem, $m$ balls are placed sequentially into $n$ initially empty bins; for each ball, $d$ bins are chosen independently and uniformly at random, with replacement. The *greedy* algorithm places each ball in the least loaded of its $d$ chosen bins. The load of a bin is the number of balls in it, and the *maximum load* is the largest load at the end. For $d = 1$ this is throwing each ball into one uniform bin, whose maximum load for $m = n$ is the [maximum load of balls into bins](../../randomized-algorithms/maximum-load-of-balls-into-bins.md).

## Depends on

- [Maximum load of balls into bins](../../randomized-algorithms/maximum-load-of-balls-into-bins.md)

## Sources

- Y. Azar, A. Z. Broder, A. R. Karlin and E. Upfal, "Balanced allocations", *SIAM Journal on Computing* 29(1):180–200, 1999, Section 2 (the finite process, the $(m, n, d)$-problem and the greedy algorithm, which assigns each ball to the box of lowest load among its $d$ choices) and Section 1 (the $d$ choices are not necessarily distinct).
