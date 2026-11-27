# A query point changes trapezoid with probability at most 4/i

Let $S$ be a set of $n$ non-crossing segments in general position, inserted in uniformly random order into the trapezoidal map with its search structure (a rooted directed acyclic graph whose internal nodes test whether a query point lies to the left or right of an endpoint or above or below a segment, and whose leaves are the trapezoids), and let $q$ be a fixed query point on no segment and on no vertical line through an endpoint. Let $X_i(q)$ be the event that the trapezoid of the map containing $q$ changes when the $i$-th segment is inserted. Then $\Pr[X_i(q)] \le 4/i$, because the trapezoid containing $q$ after $i$ insertions is determined by at most four segments and each of the $i$ segments is equally likely to be the last inserted. Since $q$ descends at most three levels of the search structure per change, the expected length of its search path is at most $3 \sum_{i=1}^n 4/i = 12 H_n = O(\log n)$.

## Depends on

- [Trapezoidal map](trapezoidal-map.md)

## Proof depends on

- [Every trapezoid is determined by at most four segments](every-trapezoid-is-determined-by-at-most-four-segments.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 9, analysis of the query time: $D(q) \le 3 \sum_i \Pr(X_i(q))$, $\Pr(X_i(q)) \le 4/i$ by backwards analysis, and $D(q) \le 12 \ln n$
