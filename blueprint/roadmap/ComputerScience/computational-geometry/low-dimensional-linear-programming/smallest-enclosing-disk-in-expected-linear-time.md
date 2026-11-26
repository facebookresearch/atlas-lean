# Smallest enclosing disk in expected linear time

The minimum enclosing disk of $n$ points in $\mathbb{R}^2$ can be computed in $O(n)$ expected time by the randomized incremental algorithm: insert the points in uniformly random order and, when a new point $p_i$ lies outside the current disk, recompute the minimum enclosing disk of $p_1, \dots, p_i$ constrained to have $p_i$ on its boundary, by the same method one level down. The expectation is over the insertion order only; in $\mathbb{R}^d$ the method takes $O((d + 1)! \, n)$ expected time.

## Depends on

- [Average formula for the expected time over random orderings](../../randomized-algorithms/average-case-running-time/expected-time-uniform-permutation.md)

## Proof depends on

- [A point outside the current disk lies on the new boundary](a-point-outside-the-current-disk-lies-on-the-new-boundary.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 21, "Minimum Enclosing Ball": expected time $O((d+1)!\,n)$ in $\mathbb{R}^d$ and the randomized incremental algorithm in the plane
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Smallest enclosing circles and more", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides4b.pdf>: the theorem that the smallest enclosing circle of $n$ points in the plane can be computed in $O(n)$ expected time
