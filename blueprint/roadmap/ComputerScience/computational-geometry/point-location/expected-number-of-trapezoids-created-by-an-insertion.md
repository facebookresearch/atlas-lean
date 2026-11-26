# Expected number of trapezoids created by an insertion

Build the trapezoidal map of a set $S$ of $n$ segments, as in its definition, by inserting the segments one at a time in an order chosen uniformly at random among all $n!$ orders, updating the map after each insertion. Let $k_i$ be the number of new trapezoids created when the $i$-th segment is inserted. Then $\mathbb{E}[k_i] = O(1)$ for every $i$, the expectation being over the insertion order only.

## Depends on

- [Trapezoidal map](trapezoidal-map.md)

## Proof depends on

- [Size of a trapezoidal map](size-of-a-trapezoidal-map.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 8, the lemma that $\mathbb{E}[k_i] = O(1)$, by backwards analysis
