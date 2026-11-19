# Noncrossing perfect matching

A function $f : \mathbb{N} \to \mathbb{N}$ is a *noncrossing perfect matching* of
$\{0, \dots, n-1\}$ if it maps $\{0, \dots, n-1\}$ to itself, has no fixed point there, is an
involution there ($f(f(i)) = i$), is the identity from $n$ on, and its arcs $\{a, f(a)\}$ are
nested or disjoint: whenever $a < b < f(a)$, also $a < f(b) < f(a)$.

The nested condition is equivalent to the absence of two interleaved arcs $a < b < f(a) < f(b)$,
the crossing condition of
[a noncrossing partition](../noncrossing-partitions-and-the-refinement-order/is-noncrossing.md)
restricted to blocks of size two. Fixing $f$ to be the identity outside $\{0, \dots, n-1\}$ makes
two matchings equal exactly when they agree on $\{0, \dots, n-1\}$.

## Background

- [Pair partition](is-pair-partition.md): the partitions these matchings encode; the
  correspondence is proved in
  [Noncrossing pair partitions are noncrossing perfect matchings](pair-partition-equiv-ncmatching.md).
