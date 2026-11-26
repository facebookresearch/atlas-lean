# k-Dollo completions characterize k-Dollo phylogeny matrices

Let $A \in \{0,1\}^{n\times m}$ record the presence ($a_{i,j}=1$) or absence of mutation $j$ in cell $i$. A **$k$-Dollo phylogeny** for $A$ is a rooted tree whose nodes are labelled by vectors in $\{0,1\}^m$, with the all-zero root (for somatic mutations), whose $n$ leaves are labelled by the rows of $A$, and in which each mutation is gained ($0 \to 1$ on an edge) at most once and lost ($1 \to 0$) on at most $k$ edges. $A$ is a **$k$-Dollo phylogeny matrix** if such a tree exists. For $k = 0$ this is the infinite-sites (perfect phylogeny) model.

A matrix $B \in \{0, \dots, k+1\}^{n \times m}$ is a **$k$-completion** of $A$ if $b_{i,j} = 1 \iff a_{i,j} = 1$ and $b_{i,j} \in \{0, 2, \dots, k+1\} \iff a_{i,j} = 0$; state $s \ge 2$ marks a cell that carries the $(s-1)$-th loss of mutation $j$. Writing $I^{(i)} = \{i, \dots, k+1\}$, $B$ is a **$k$-Dollo completion** if no two columns and three rows of $B$ form any of

$$\begin{pmatrix} i_1 & 0\\ 0 & j_1\\ i_1' & j_1'\end{pmatrix},\quad \begin{pmatrix} i_1 & j_1''\\ 0 & j_2\\ i_1' & j_2\end{pmatrix},\quad \begin{pmatrix} i_2 & 0\\ i_1'' & j_1\\ i_2 & j_1'\end{pmatrix},\quad \begin{pmatrix} i_2 & j_1''\\ i_1'' & j_2\\ i_2 & j_2\end{pmatrix},$$

with $i_1, i_1', j_1, j_1' \in I^{(1)}$, $i_2, j_2 \in I^{(2)}$, $i_1'' \in I^{(1)}\setminus\{i_2\}$ and $j_1'' \in I^{(1)} \setminus \{j_2\}$. There are $(k+1)^4 + 2k^2(k+1)^2 + k^4$ forbidden $3 \times 2$ submatrices.

**Theorem.** $A$ is a $k$-Dollo phylogeny matrix if and only if it has a $k$-Dollo completion $B$.

## Depends on

- [Perfect phylogeny](../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/is-perfect-phylogeny.md)
- [Four-gamete condition for compatibility](../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/compatible-iff-not-four-gametes.md)

## Expansion

Relabelling each lost entry by the index of the loss event turns the $k$-Dollo phylogeny into a multi-state perfect phylogeny in which every state of every character arises exactly once, on a tree where state $1$ descends from $0$ and each loss state $s \ge 2$ descends from $1$. The forbidden submatrices generalize the four-gamete obstruction of the binary case: they are two-character patterns that no tree with this state-tree structure can display, and the theorem (proved in the SPhyR paper) states that excluding them is also sufficient.

## Sources

- P. Sashittal, H. Zhang, C. A. Iacobuzio-Donahue and B. J. Raphael, "ConDoR: tumor phylogeny inference with a copy-number constrained mutation loss model", Genome Biology 24 (2023), Methods ("Characterization of constrained k-Dollo phylogenies"), Definitions 2–3 and Theorem 1, <https://doi.org/10.1186/s13059-023-03106-5>, PMCID: PMC10688497.
- M. El-Kebir, "SPhyR: tumor phylogeny estimation from single-cell sequencing data under loss and error", Bioinformatics 34 (2018), i671–i679, <https://doi.org/10.1093/bioinformatics/bty589>.
