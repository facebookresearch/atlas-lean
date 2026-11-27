# Short-reconvergence partition of a de Bruijn graph

Let $G$ be a directed graph (the de Bruijn graph of $k$-mers from metagenomic reads) and $w \ge 1$
a length bound. A subgraph $C$ has the *short-reconvergence property* if for every vertex $u$ of
$C$ there is a vertex $v$ of $C$ such that either

1. for each outgoing edge $e$ of $u$ there is a path in $C$ of length at most $w$ from $u$ to $v$
   that starts with $e$, or
2. for each incoming edge $e$ of $u$ there is a path in $C$ of length at most $w$ from $v$ to $u$
   that ends with $e$.

In a graph $H$, a vertex $u$ *passes the outgoing test* if some vertex $v$ is reachable from $u$
by a path in $H$ of length at most $w$ starting with $e$, for every outgoing edge $e$ of $u$ in
$H$; the *incoming test* is defined symmetrically. The greedy algorithm repeatedly examines each
vertex $u$ of the current graph: if $u$ has outgoing edges and fails the outgoing test, it deletes
all outgoing edges of $u$, and symmetrically for incoming edges; it stops when no deletion applies.

**Theorem.** Let $G^\ast$ be the graph at termination. Every vertex of $G^\ast$ passes the
outgoing test or has no outgoing edges in $G^\ast$, and passes the incoming test or has no incoming
edges in $G^\ast$. Consequently every connected component of $G^\ast$ has the short-reconvergence
property.

**Remark (no maximality).** The algorithm does not in general return the maximal connected
components of $G$ with the short-reconvergence property, and it may delete edges of such a
component. Take $w = 2$ and the edges $s \to a$, $s \to b$, $a \to u$, $b \to u$, $u \to c$,
$u \to d$. In $G$, the vertices $s, a, b$ satisfy condition 1 with $v = u$, the vertex $u$
satisfies condition 2 with $v = s$, and $c, d$ satisfy condition 2 with $v = u$, so $G$ itself is
the unique maximal component with the property. The vertex $u$ fails the outgoing test ($c$ and
$d$ have no common reachable vertex), so the algorithm deletes $u \to c$ and $u \to d$ and returns
the components $\{s, a, b, u\}$, $\{c\}$, $\{d\}$. The source states (its Theorem 1) that the
greedy algorithm solves the problem of finding the maximal components; its inductive proof treats
the failure of one directional test as a violation of the property, which is defined by an "or",
and this example shows the stronger claim is false. The page states only what the algorithm
guarantees.

## Depends on

- [de Bruijn graph genome assembly](../../de-bruijn-graph-genome-assembly/README.md)

## Expansion

At termination no deletion applies, which is exactly the first statement. For the second, let $C$
be a connected component of $G^\ast$ and $u$ a vertex of $C$. If $u$ has outgoing edges in
$G^\ast$, it passes the outgoing test with some vertex $v$, and the witnessing paths start at $u$,
so they and $v$ lie in $C$; condition 1 holds. If $u$ has no outgoing edges, condition 1 holds
vacuously with $v = u$. Either way $u$ satisfies the property in $C$ (in fact both directional
conditions hold at every vertex, which is stronger than the "or" in the definition). The
biological rationale: genomes of subspecies of one species share $k$-mers densely, so where they
diverge (a bubble of variant paths) the paths meet again at a shared $k$-mer within a short
distance $w$ (for example $300$ bp with $k = 50$), while genomes of different species share
$k$-mers only sporadically, so a branch created by a region common to two species does not
reconverge quickly. Deleting the edges at vertices whose branches fail to reconverge therefore
tends to separate species while keeping within-species variation inside a component. Components
are then joined by paired-end reads and turned into consensus contigs by multiple alignment of
their simple paths.

## Sources

- Y. Peng, H. C. M. Leung, S. M. Yiu, F. Y. L. Chin, "Meta-IDBA: a de Novo assembler for metagenomic
  data", Bioinformatics 27 (2011) i94-i101, Section 2.2, "Divide graph into connected components",
  graph partition problem, greedy algorithm and Theorem 1 (whose maximality claim is corrected
  above), <https://doi.org/10.1093/bioinformatics/btr216> (PMC3117360).
