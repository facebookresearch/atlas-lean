# Point location by randomized incremental trapezoidal maps

Let $S$ be a set of $n$ segments as in the definition of the trapezoidal map. Insert them in uniformly random order, maintaining the trapezoidal map together with a search structure, a rooted directed acyclic graph whose internal nodes test whether a query point lies to the left or right of an endpoint or above or below a segment and whose leaves are the trapezoids. Then the expected construction time is $O(n \log n)$ and the expected size of the search structure is $O(n)$; and for every fixed query point $q$ that lies on no segment and on no vertical line through an endpoint, the expected length of the search path for $q$ is $O(\log n)$. All expectations are over the insertion order only.

## Depends on

- [Trapezoidal map](trapezoidal-map.md)
- [Average formula for the expected time over random orderings](../../randomized-algorithms/average-case-running-time/expected-time-uniform-permutation.md)

## Proof depends on

- [Expected number of trapezoids created by an insertion](expected-number-of-trapezoids-created-by-an-insertion.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 9, "Analysis": $O(n)$ expected size and $O(\log n)$ expected query time for a fixed query point
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Planar point location", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides6.pdf>: the theorem on preprocessing a subdivision of $n$ non-crossing segments in $O(n \log n)$ expected time with $O(n)$ expected storage
