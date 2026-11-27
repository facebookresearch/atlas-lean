# Parsimonious UMI graph and NP-completeness of monochromatic arborescence cover

Fix one cell. Each observed read carries a UMI $u$ and maps to an **equivalence class** $T \subseteq \mathcal T$, the set of transcripts it is compatible with. The **parsimonious UMI graph** (PUG) $G = (V, E)$ has one vertex $v_i = (u_i, T_i)$ per distinct observed pair, with count $c_i$ (number of reads), and edges, with $d$ the Hamming distance:

- a **directed** edge $v_i \to v_j$ whenever $c_i > 2c_j - 1$, $|T_i \cap T_j| > 0$ and $d(u_i, u_j) = 1$ (so $v_j$ may be a PCR or sequencing error of $v_i$);
- a **bi-directed** edge between $v_k, v_\ell$ not joined by a directed edge whenever $d(u_k, u_\ell) \le 1$ and $|T_k \cap T_\ell| > 0$ (the two may be reads of one molecule from different fragmentation positions).

Treat the elements of $T_i$ as the *colours* of $v_i$. An **arborescence** in $G$ is a rooted subtree in which every vertex is reached by exactly one directed path from the root; it is **monochromatic** if the colour sets of its vertices have nonempty common intersection, so that one transcript explains all of it. Each monochromatic arborescence models one pre-PCR molecule.

**Problem (minimum monochromatic arborescence cover).** Given $G$ and $k$, decide whether $V$ can be partitioned into at most $k$ vertex-disjoint monochromatic arborescences.

**Theorem.** Minimum cardinality covering by monochromatic arborescences is NP-complete.

## Proof depends on

- [DOMINATING SET ON BIPARTITE GRAPHS is NP-complete](../../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/dominating-set-on-restricted-graph-classes/dominating-set-bipartite-np-complete.md)

## Expansion

Membership in NP is immediate. Hardness is by reduction from dominating set: given an undirected graph $H = (V, F)$, replace each edge by a bi-directed edge and give vertex $i$ the colour set $T_i = \{i\} \cup \{j : \{i, j\} \in F\}$. A dominating set $D$ yields $|D|$ stars, each rooted at $x \in D$ and coloured $x$, covering $V$. Conversely, the colour $\ell$ of a monochromatic arborescence lies in every vertex's set, so vertex $\ell$ belongs to it and is adjacent to all its other vertices; the colours of $k$ covering arborescences form a dominating set of size $k$. In practice the cover is computed greedily per weakly connected component: repeatedly take the (vertex, transcript) pair whose breadth-first monochromatic arborescence is largest and delete it. An arborescence whose admissible colours span several genes is resolved by an EM allocation of counts proportional to gene abundance (no length effect for tagged-end protocols).

## Sources

- A. Srivastava, L. Malik, T. Smith, I. Sudbery, R. Patro, "Alevin efficiently estimates accurate gene abundances from dscRNA-seq data", Genome Biology 20 (2019) 65, Materials and methods ("UMI resolution algorithm"), Theorem 1 and its proof, <https://doi.org/10.1186/s13059-019-1670-y>, PMCID PMC6437997.
