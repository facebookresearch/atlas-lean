# Perfect phylogeny mixture and the sum condition

Let $F = (f_{i,j}) \in [0,1]^{n \times m}$ record, for each of $n$ samples (or cells), the fraction $f_{i,j}$ of genomes carrying mutation $j \in \{1,\dots,m\}$. Under the infinite-sites assumption a **clone matrix** $B \in \{0,1\}^{(m+1) \times m}$ is a perfect phylogeny matrix: its rows are the wild type (clone $0$) and $m$ clones, clone $\ell$ carrying mutation $j$ iff $j$ labels an edge on the root-to-$\ell$ path of a rooted **clone tree** $S$ on vertices $\{0,\dots,m\}$. A **mixture matrix** $U \in [0,1]^{n \times (m+1)}$ has rows summing to $1$ (clone proportions per sample). The **perfect phylogeny mixture (PPM) problem** asks for a factorization $F = UB$.

The **ancestry graph** $G$ of $F$ is the directed graph on $\{0, 1, \dots, m\}$ with an edge $(j, j')$ iff $j = 0$, or $f_{i,j} \ge f_{i,j'}$ for every row $i$. For a spanning arborescence $H$ of $G$ rooted at $0$, write $\delta^+_H(j)$ for the children of $j$.

**Theorem.** $F$ admits a solution to the PPM problem if and only if $G$ has a spanning arborescence $H$ rooted at $0$ satisfying the **sum condition**

$$f_{i,j} \ \ge \sum_{j' \in \delta^+_H(j)} f_{i,j'} \qquad \text{for all } i \in \{1,\dots,n\},\ j \in \{0,1,\dots,m\},$$

with $f_{i,0} := 1$. The arborescence $H$, with the edge into vertex $j$ labelled by mutation $j$, is then the clone tree $S$ determining $B$.

## Expansion

If $F = UB$ with $B$ given by a clone tree $S$, then $f_{i,j}$ is the total proportion in sample $i$ of the subtree of $S$ below the edge carrying mutation $j$; descendants therefore never exceed ancestors (so $S \subseteq G$), and the subtrees of the children of $j$ are disjoint parts of the subtree of $j$, giving the sum condition. Conversely, given $H$ satisfying the sum condition, set $u_{i,j} = f_{i,j} - \sum_{j' \in \delta^+_H(j)} f_{i,j'} \ge 0$ (and $u_{i,0} = 1 - \sum_{j' \in \delta^+_H(0)} f_{i,j'}$); telescoping over subtrees shows the rows of $U$ sum to $1$ and $F = UB$. Different arborescences may satisfy the condition, so solutions are generally not unique.

## Sources

- P. Sashittal, V. Chen, A. Pasarkar, B. J. Raphael, "Joint inference of cell lineage and mitochondrial evolution from single-cell sequencing data", *Bioinformatics* (2024), Sections 2–3 (Problem 0.1, ancestry graph, Theorem 1, restating the characterization of El-Kebir et al. 2015), <https://doi.org/10.1093/bioinformatics/btae231> (PMC11211840).
