# Copy-number balance and alternating-walk decomposition of a diploid interval adjacency graph

Partition a diploid reference genome into segments $1, \dots, m$, each present on haplotypes $H \in \{A, B\}$ with tail and head extremities $\sigma \in \{t, h\}$. The **diploid interval adjacency graph** (DIAG) has vertex set
$$V = \{\, j_H^\sigma : j \in \{1,\dots,m\},\ \sigma \in \{t,h\},\ H \in \{A,B\} \,\}$$
and two kinds of edges: **segment edges** $E_S = \{\{j_H^t, j_H^h\}\}$, and **adjacency edges** $E_A = E_R \cup E_N$, where $E_R$ joins extremities adjacent in the reference and $E_N$ represents haplotype-labelled novel adjacencies (rearrangement breakpoints), self-loops allowed. Each vertex $v$ meets exactly one segment edge $e_S(v)$, at most one reference adjacency edge $e_R(v)$, and a set $E_N(v)$ of novel adjacency edges. A derived genome gives a multiplicity $\mu : E \to \mathbb{N}$ counting how often each segment and adjacency is used. Let $l(e) = 2$ for a self-loop and $l(e) = 1$ otherwise. Vertex $v$ is **copy-number balanced** if
$$\mu\big(e_S(v)\big) = \mu\big(e_R(v)\big) + \sum_{e \in E_N(v)} l(e)\,\mu(e),$$
and has **copy-number excess** if the left side is strictly larger.

**Theorem.** A weighted DIAG $(V, E, \mu)$ can be partitioned into segment–adjacency alternating walks that start and end at a set $T \subseteq V$ of telomere vertices, traversing every edge $e$ exactly $\mu(e)$ times, provided every non-telomere vertex is copy-number balanced and every telomere vertex in $T$ has copy-number excess. When circular chromosomes are allowed, the balance conditions are also sufficient for a derived genome with these segment and adjacency copy numbers to exist.

Each walk spells a derived chromosome as a concatenation of reference segments, so the reconstruction of clone- and haplotype-specific karyotypes from bulk tumour data becomes the search for clone-specific multiplicities $\mu_i$ satisfying these balance conditions, consistent with allele-specific copy numbers and with each unlabeled novel adjacency assigned to haplotypes, while minimizing a deviation from the observed read-depth-derived copy numbers.

## Expansion

At a balanced vertex, each traversal of the segment edge can be paired with one traversal of an incident adjacency edge (a self-loop is entered and left at the same vertex, hence the factor $2$), so walks can be extended through every non-telomere vertex; unmatched segment traversals at excess vertices are where walks end. This is an Eulerian-type decomposition of an edge-coloured multigraph with alternation constraints (Kotzig; Pevzner). Linear chromosomes need additional conditions, so the theorem is sufficient but the existence question for linear-only genomes is stricter.

## Sources

- S. Aganezov and B. J. Raphael, "Reconstruction of clone- and haplotype-specific cancer genome karyotypes from bulk tumor samples", Genome Research 30 (2020), 1274–1290, Methods ("Diploid interval adjacency graph"), Theorem 1, <https://doi.org/10.1101/gr.256701.119>, PMCID: PMC7545144.
- A. Kotzig, "Moves without forbidden transitions in a graph", Matematický časopis 18 (1968), 76–80.
