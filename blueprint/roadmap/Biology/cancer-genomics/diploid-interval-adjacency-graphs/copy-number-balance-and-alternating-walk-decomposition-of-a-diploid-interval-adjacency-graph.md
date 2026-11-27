# Copy-number balance and alternating-walk decomposition of a diploid interval adjacency graph

Partition a diploid reference genome into segments $1, \dots, m$, each present on haplotypes $H \in \{A, B\}$ with tail and head extremities $\sigma \in \{t, h\}$. The **diploid interval adjacency graph** (DIAG) has vertex set

$$V = \{\, j_H^\sigma : j \in \{1,\dots,m\},\ \sigma \in \{t,h\},\ H \in \{A,B\} \,\}$$

and two kinds of edges: **segment edges** $E_S = \{\{j_H^t, j_H^h\}\}$, and **adjacency edges** $E_A = E_R \cup E_N$, where $E_R$ joins extremities adjacent in the reference and $E_N$ represents haplotype-labelled novel adjacencies (rearrangement breakpoints), self-loops allowed. Each vertex $v$ meets exactly one segment edge $e_S(v)$, at most one reference adjacency edge $e_R(v)$, and a set $E_N(v)$ of novel adjacency edges. A derived genome gives a multiplicity $\mu : E \to \mathbb{N}$ counting how often each segment and adjacency is used. Let $l(e) = 2$ for a self-loop and $l(e) = 1$ otherwise. Vertex $v$ is **copy-number balanced** if

$$\mu\big(e_S(v)\big) = \mu\big(e_R(v)\big) + \sum_{e \in E_N(v)} l(e)\,\mu(e),$$

and has **copy-number excess** if the left side is strictly larger.

**Theorem.** Let $(V, E, \mu)$ be a weighted DIAG and $T \subseteq V$ a set of telomere vertices such that every vertex of $V \setminus T$ is copy-number balanced and every vertex of $T$ has copy-number excess. Then the edge copies ($\mu(e)$ copies of each edge $e$) partition into segment–adjacency alternating walks, each either an *open* walk that starts and ends at vertices of $T$ with segment edges, or a *closed* alternating walk; at each $t \in T$ exactly the excess of $t$ open-walk ends occur. If moreover every connected component of the subgraph of edges with $\mu(e) > 0$ contains a vertex of $T$, the partition can be chosen with open walks only.

Balance and excess alone do not force open walks: a balanced cycle of positive multiplicity disjoint from $T$ is covered only by closed walks, and the original unweighted graph being connected does not make its positive-multiplicity support connected. A closed walk spells a circular chromosome, so when circular chromosomes are allowed the conditions suffice for a derived genome with these segment and adjacency copy numbers; for linear chromosomes only, the support condition above is needed as well. This is the path–cycle decomposition that Aganezov and Raphael distinguish from the linear case.

Each walk spells a derived chromosome as a concatenation of reference segments, so the reconstruction of clone- and haplotype-specific karyotypes from bulk tumour data becomes the search for clone-specific multiplicities $\mu_i$ satisfying these balance conditions, consistent with allele-specific copy numbers and with each unlabeled novel adjacency assigned to haplotypes, while minimizing a deviation from the observed read-depth-derived copy numbers.

## Expansion

At a balanced vertex, each traversal of the segment edge can be paired with one traversal of an incident adjacency edge (a self-loop is entered and left at the same vertex, hence the factor $2$), so walks extend through every non-telomere vertex; the unmatched segment traversals at an excess vertex are where open walks end. In each connected component of the positive-multiplicity subgraph the total excess is even, since the segment-degree and adjacency-degree sums are both even. Joining these ends in pairs by new adjacency-coloured edges makes every vertex balanced, and Kotzig's theorem for two-edge-coloured multigraphs gives an alternating Eulerian circuit per component; cutting it at the new edges yields open walks, and a component without new edges stays one closed walk.

## Sources

- S. Aganezov and B. J. Raphael, "Reconstruction of clone- and haplotype-specific cancer genome karyotypes from bulk tumor samples", Genome Research 30 (2020), 1274–1290, Methods ("Diploid interval adjacency graph"), Theorem 1, and Supplemental Methods ("On minimal path-cycle Eulerian decomposition of (D)IAGs"), <https://doi.org/10.1101/gr.256701.119>, PMCID: PMC7545144.
- A. Kotzig, "Moves without forbidden transitions in a graph", Matematický časopis 18 (1968), 76–80.
