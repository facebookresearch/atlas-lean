# Lindström–Gessel–Viennot lemma

Let $R$ be a commutative ring, let $n$ be a natural
number, and let $E$ be a relation on a type $V$, read as a directed graph on $V$ with an edge
from $u$ to $v$ whenever $E(u, v)$. Suppose there is a function $r : V \to \mathbb{N}$ with
$r(u) < r(v)$ whenever $E(u, v)$, so the graph is acyclic. A path from $u$ to $w$ is a nonempty
list of vertices that starts at $u$, ends at $w$, and in which there is an edge from each vertex
to the next one. Let $A_0, \dots, A_{n-1}$ and $B_0, \dots, B_{n-1}$ be vertices, and suppose
that for all $i, j < n$ the paths from $A_i$ to $B_j$ form a finite set $P_{ij}$. Let $e$ be the
$n \times n$ matrix over $R$ with $e_{ij} = |P_{ij}|$. Suppose further that whenever $i < j$ and
$l < k$, every path from $A_i$ to $B_k$ shares a vertex with every path from $A_j$ to $B_l$. Let
$S$ be the finite set of families $(F_0, \dots, F_{n-1})$ in which each $F_i$ is a path from
$A_i$ to $B_i$ and $F_i$ and $F_j$ share no vertex whenever $i \ne j$. Then the number of
elements of $S$, taken in $R$, equals $\det e$.

## Sources

- https://en.wikipedia.org/wiki/Lindstr%C3%B6m%E2%80%93Gessel%E2%80%93Viennot_lemma
