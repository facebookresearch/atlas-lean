# Divide-and-conquer core of maximum subarray

For lists over an additive monoid with a
linear order: on the empty list it returns $0$ and on a one-element list $[x]$ it returns $x$,
both at no cost. On a list of length $n \ge 2$, let $m = \lfloor n/2 \rfloor$, let $l$ and $r$ be
its results on the first $m$ elements and on the remaining $n - m$ elements, let $s$ be the best
nonempty suffix sum of the first $m$ elements as computed by the suffix scan, and let $p$ be the
prefix scan of the remaining elements. It returns $\max(\max(l, r), s + p)$, at the cost of
these four computations plus $3$.
