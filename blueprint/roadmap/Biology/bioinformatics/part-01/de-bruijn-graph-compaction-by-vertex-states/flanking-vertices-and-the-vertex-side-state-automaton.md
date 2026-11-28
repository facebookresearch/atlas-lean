# Flanking vertices and the vertex-side state automaton

**Setting.** Let $S$ be a collection of genome sequences and $G(S, k)$ its bidirected node-centric de Bruijn graph: vertices are canonical $k$-mers (a $k$-mer identified with its reverse complement), each vertex $v$ has two sides (front and back), and each occurrence of a $(k+1)$-mer in $S$ gives an edge joining a side of its prefix vertex to a side of its suffix vertex. A side to which a sequence of $S$ starts or ends (a sentinel side) is given an extra placeholder edge $\epsilon$.

**Side multiplicity.** Every side has at most four distinct non-$\epsilon$ incident edges, one for each base that can extend the $k$-mer on that side.

**Flanking vertices.** Let $p$ be a maximal unitig (maximal non-branching path) and $v$ an endpoint of $p$, entered through side $s^{\mathrm{in}}_v$, with opposite side $s^{\mathrm{out}}_v$. Then $p$ cannot be extended through $s^{\mathrm{out}}_v$ exactly when

1. $s^{\mathrm{out}}_v$ has more than one incident edge (counting $\epsilon$), or
2. $s^{\mathrm{out}}_v$ has exactly one incident edge, joining it to a side $s_u$ of a vertex $u$, and $s_u$ has more than one incident edge.

Every vertex is therefore either *flanking* (an endpoint of its maximal unitig) or *internal*, and the maximal unitigs are the walks in $G(S, k)$ between flanking vertices, so compaction reduces to classifying vertices.

**Finite state per vertex.** For the classification, a side needs only one of five configurations: "exactly one distinct edge so far, extending by base $X \in \{A, C, G, T\}$" (four configurations) or "more than one distinct edge, or an $\epsilon$ edge". A vertex thus has $5 \times 5 = 25$ states, plus an initial unvisited state $q_0$. Treating each vertex as a deterministic finite automaton $(Q, \Sigma', \delta, q_0, Q')$ with $|Q| = 26$, whose input symbols are the (front, back) extension pairs seen at an occurrence of the $k$-mer in $S$, one pass over $S$ computes every final state. The transitions are monotone: a side in a singleton configuration either stays (same base seen again) or moves to the multi configuration (different base or sentinel), and the multi configuration is absorbing. The final state of $v$ and of its neighbours along a walk decide conditions 1–2, and a second pass over $S$ outputs each maximal unitig once.

## Expansion

A non-trivial unitig requires every internal step to leave a side with a single edge and enter a side with a single edge; condition 1 breaks the first requirement at $v$, condition 2 breaks the second at $u$, and for a single-$k$-mer unitig either condition prevents growth. Because the state set is finite and transitions only move toward "multi", the order in which occurrences are processed does not affect the final state, so the pass parallelizes over sequences with lock-free updates to a per-vertex state table indexed by a minimal perfect hash of the $k$-mer set. The memory cost is a constant number of bits per distinct $k$-mer (five bits suffice for 26 states), independent of the number of edges, which is what lets the method compact graphs built from thousands of reference genomes.

## Sources

- J. Khan, R. Patro, "Cuttlefish: fast, parallel and low-memory compaction of de Bruijn graphs from large-scale genome collections", Bioinformatics 37 (Supplement 1) (2021) i177–i186, Sections 4.2 ("Flanking vertices of the maximal unitigs"), 4.3 ("A deterministic finite-state automaton model for vertices"), 4.5 and 4.7, <https://doi.org/10.1093/bioinformatics/btab309> (PMC8275350).
