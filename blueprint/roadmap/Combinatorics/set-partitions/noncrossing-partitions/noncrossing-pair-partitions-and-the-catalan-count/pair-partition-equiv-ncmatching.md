# Noncrossing pair partitions are noncrossing perfect matchings

The [partner map](pair-partner.md) is a bijection from the noncrossing pair partitions of
$\{0, \dots, n-1\}$ to the [noncrossing perfect matchings](is-ncmatching.md) of
$\{0, \dots, n-1\}$, with inverse [the pair partition of a matching](matching-partition.md).

The two noncrossing conditions agree: two blocks $\{a, c\}$ and $\{b, d\}$ of a pair partition cross
($a < b < c < d$) exactly when the partner map $f$ has $a < b < f(a) < f(b)$, and the nested
condition fails at $(a, b)$ exactly when $f(b) < a$ (a crossing $f(b) < a < b < f(a)$) or
$f(b) > f(a)$.

## Background

- [Noncrossing partitions](../noncrossing-partitions-and-the-refinement-order/is-noncrossing.md):
  the crossing condition on the partition side.
