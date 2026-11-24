# Weighted Lindström–Gessel–Viennot lemma, noncrossing form

Let $R$ be a commutative ring, let $n$ be a natural number, and let $E$ be a relation on a set $V$, read as a
directed graph with an edge from $u$ to $v$ whenever $E(u, v)$. Suppose there is a function $r : V \to \mathbb{N}$
with $r(u) < r(v)$ whenever $E(u, v)$, so the graph is acyclic. A path from $u$ to $x$ is a nonempty list of
vertices that starts at $u$, ends at $x$, and has an edge from each vertex to the next. Let $w : V \times V \to R$ be
edge weights, let $A_0, \dots, A_{n-1}$ and $B_0, \dots, B_{n-1}$ be vertices, and suppose that for all $i, j < n$ the
paths from $A_i$ to $B_j$ form a finite set $P_{ij}$. Let $e$ be the $n \times n$ matrix over $R$ with
$e_{ij} = \sum_{p \in P_{ij}} w(p)$, where $w(p)$ is the [weight of the path](lgv-path-weight.md) $p$. Suppose that
whenever $i < j$ and $l < k$, every path from $A_i$ to $B_k$ shares a vertex with every path from $A_j$ to $B_l$.
Let $S$ be the set of families $(F_0, \dots, F_{n-1})$ in which each $F_i$ is a path from $A_i$ to $B_i$ and $F_i$
and $F_j$ share no vertex whenever $i \ne j$. Then

$$\sum_{F \in S} \prod_{i < n} w(F_i) = \det e.$$

The noncrossing hypothesis replaces the planar embedding of the source, where sources and sinks lie in order on the
boundary: it is what forces every vertex-disjoint family to connect $A_i$ to $B_i$, so that only the identity
permutation survives the sign-reversing involution.

## Background

- [Lindström–Gessel–Viennot lemma](lindstrom-gessel-viennot.md): the unit-weight case, which counts nonintersecting path systems.
- [Total positivity](../../../LinearAlgebra/special-matrices/total-positivity/README.md): the lemma's main application, total nonnegativity of weight matrices of planar networks (Fomin–Zelevinsky, Corollaries 2 and 3).

## Sources

- Sergey Fomin and Andrei Zelevinsky, *Total positivity: tests and parametrizations*, Math. Intelligencer 22 (2000),
  no. 1, 23–33, arXiv:math/9912128v1, Lemma 1, case $I = J = [1, n]$, which that paper traces to Lindström,
  Karlin–McGregor and Gessel–Viennot.
