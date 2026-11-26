# Short-reconvergence partition of a de Bruijn graph

Let $G$ be a directed graph (the de Bruijn graph of $k$-mers from metagenomic reads) and $w \ge 1$
a length bound. A subgraph $C$ has the *short-reconvergence property* if for every vertex $u$ of
$C$ there is a vertex $v$ of $C$ such that either

1. for each outgoing edge $e$ of $u$ there is a path in $C$ of length at most $w$ from $u$ to $v$
   that starts with $e$, or
2. for each incoming edge $e$ of $u$ there is a path in $C$ of length at most $w$ from $v$ to $u$
   that ends with $e$.

The *graph partition problem* asks for the maximal connected components of $G$ with this property.
The greedy algorithm repeatedly examines each vertex $u$ of the current graph: if no vertex $v$ is
reachable within distance $w$ along every outgoing edge of $u$, it deletes all outgoing edges of
$u$, and symmetrically for incoming edges; it stops when no deletion applies.

**Theorem.** The greedy algorithm solves the graph partition problem: no deleted edge belongs to
any component with the short-reconvergence property, and the connected components of the final
graph are the maximal such components.

## Depends on

- [de Bruijn graph genome assembly](../../de-bruijn-graph-genome-assembly/README.md)

## Expansion

Genomes of subspecies of one species share $k$-mers densely, so where they diverge (a bubble of
variant paths) the paths meet again at a shared $k$-mer within a short distance $w$ (for example
$300$ bp with $k = 50$). Genomes of different species share $k$-mers only sporadically, so a branch
created by a region common to two species does not reconverge quickly. Deleting the edges at
vertices whose branches fail to reconverge therefore separates species while keeping the
within-species variation inside a component. The proof is by induction on the deleted edges: the
first deleted edge cannot lie in a valid component, since the reconvergence test already failed in
all of $G$, and if $e_1, \dots, e_{k-1}$ lie in no valid component, the test that deletes $e_k$
fails in $G \setminus \{e_1, \dots, e_{k-1}\}$, which contains every valid component, so $e_k$ lies in
none either. Components are then joined by paired-end reads and turned into consensus contigs by
multiple alignment of their simple paths.

## Sources

- Y. Peng, H. C. M. Leung, S. M. Yiu, F. Y. L. Chin, "Meta-IDBA: a de Novo assembler for metagenomic
  data", Bioinformatics 27 (2011) i94-i101, Section 2.2, "Divide graph into connected components",
  graph partition problem and Theorem 1, <https://doi.org/10.1093/bioinformatics/btr216>
  (PMC3117360).
