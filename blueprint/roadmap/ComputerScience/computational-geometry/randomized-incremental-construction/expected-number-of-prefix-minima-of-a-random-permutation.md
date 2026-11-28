# Expected number of prefix minima of a random permutation

Let $x_1, \dots, x_n$ be distinct real numbers listed in uniformly random order, and scan them while keeping the smallest value seen so far. For each $i$, the $i$-th value scanned is smaller than all earlier ones with probability exactly $1/i$, since the minimum of the first $i$ values is equally likely to be in each of the $i$ positions. Hence the expected number of prefix minima, the first value included, is the harmonic number $H_n = \sum_{i=1}^n 1/i = \ln n + O(1)$.

This is the simplest instance of *backwards analysis*: one fixes the set of the first $i$ elements and asks for the probability that the last of them caused the change.

## Depends on

- [Uniformly random rearrangement of a list](../../randomized-algorithms/average-case-running-time/uniform-permutation.md)

## Related topics

- [Average formula for the expected time over random orderings](../../randomized-algorithms/average-case-running-time/expected-time-uniform-permutation.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 7, "Computing the Minimum": $p_i = 1/i$ by working backwards, and $C(n) = \sum_i p_i = \ln n + O(1)$
