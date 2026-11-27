# Smallest enclosing disk in expected linear time

The minimum enclosing disk of $n \ge 1$ points in $\mathbb{R}^2$, in any position, can be computed in $O(n)$ expected time by the randomized incremental algorithm: insert the points in uniformly random order and, when a new point $p_i$ lies outside the current disk, recompute the smallest disk enclosing $p_1, \dots, p_{i-1}$ with $p_i$ on its boundary, by the same method one level down; there, when a point $p_j$ lies outside the current disk, compute the smallest disk enclosing $p_1, \dots, p_{j-1}$ with $p_i$ and $p_j$ on its boundary, which is determined directly in $O(j)$ time. The expectation is over the insertion order only. By backwards analysis, since such a disk is determined by at most three points counting the prescribed ones (for finite sets $Q$ and $R$ with $|R| \le 2$ and $Q \cup R \ne \emptyset$, if the smallest disk containing $Q$ with $R$ on its boundary exists, it is also the one for some $Q' \subseteq Q$ with $|Q'| \le 3 - |R|$), the $i$-th insertion triggers a recomputation with probability at most $3/i$ at the top level and at most $2/j$ one level down.

## Depends on

- [Average formula for the expected time over random orderings](../../randomized-algorithms/average-case-running-time/expected-time-uniform-permutation.md)

## Proof depends on

- [A point outside the current disk lies on the new boundary](a-point-outside-the-current-disk-lies-on-the-new-boundary.md)

## Expansion

This page becomes ready once:

- Proof prerequisite: the support lemma, as a page of its own: for finite sets $Q, R \subseteq \mathbb{R}^2$ with $|R| \le 2$ and $Q \cup R \ne \emptyset$, if the smallest disk containing $Q$ with $R$ on its boundary exists, it is also the smallest one for some $Q' \subseteq Q$ with $|Q'| \le 3 - |R|$. The existing structure page assumes that no four points lie on a circle and has no prescribed boundary points.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 21, "Minimum Enclosing Ball": the randomized incremental algorithm in the plane (the notes also state an $O((d+1)!\,n)$ bound for balls in $\mathbb{R}^d$, which is not part of this page)
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Smallest enclosing circles and more", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides4b.pdf>: slides 15–29, the algorithm with one and with two points prescribed on the boundary, and printed slide 48, the theorem that the smallest enclosing circle of $n$ points in the plane can be computed in $O(n)$ expected time
