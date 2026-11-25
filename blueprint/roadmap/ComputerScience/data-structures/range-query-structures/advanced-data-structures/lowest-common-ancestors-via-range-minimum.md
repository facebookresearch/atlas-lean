# Lowest common ancestors via range minimum queries

For a rooted tree with $n$ nodes, let $E$ be the sequence of nodes visited by an Euler tour (length $2n - 1$), $D$ the corresponding depths and $\mathrm{first}(u)$ the first index of $u$ in $E$. Then the lowest common ancestor of $u$ and $v$ is $E[i]$, where $i$ minimizes $D$ on the interval between $\mathrm{first}(u)$ and $\mathrm{first}(v)$. With a sparse table for range minimum queries this gives $O(n \log n)$ preprocessing and $O(1)$-time queries.

## Proof depends on

- [Correctness of sparse table queries](../sparse-table/query-build.md)

## Expansion

This page becomes ready once:

- Preprocessing and query cost of sparse tables (proof prerequisite; not yet stated)

## Sources

- M. A. Bender and M. Farach-Colton, "The LCA problem revisited", *LATIN 2000*, LNCS 1776, Springer, 2000
