# Asymptotic count of general phylogenetic networks with few reticulations

**Definitions.** A (binary, rooted) phylogenetic network is a connected DAG whose vertices are a root (indegree $0$, outdegree $2$), leaves (indegree $1$, outdegree $0$), tree vertices (indegree $1$, outdegree $2$) and reticulation vertices (indegree $2$, outdegree $1$). A *general* network imposes no further restriction (in particular it need not be tree-child, and multiple edges are not excluded a priori). It is *vertex-labeled* if all $n$ vertices carry distinct labels and *leaf-labeled* if only the $\ell$ leaves do. Let $G_{k,n}$ and $\tilde G_{k,\ell}$ count general networks with exactly $k$ reticulation vertices in the two labelings.

**Theorem.** Fix $k\ge1$.

1. *(Vertex-labeled.)* There is a constant $d_k>0$ such that, as $n\to\infty$,

$$G_{k,n}\sim d_k\bigl(1-(-1)^n\bigr)\Bigl(\frac{\sqrt2}{e}\Bigr)^n n^{\,n+2k-1},\qquad d_1=\frac{\sqrt2}{4},\ d_2=\frac{\sqrt2}{32},\ d_3=\frac{\sqrt2}{384}.$$

2. *(Leaf-labeled.)* As $\ell\to\infty$,

$$\tilde G_{k,\ell}\sim2^{3k-1}d_k\Bigl(\frac2e\Bigr)^{\ell}\ell^{\,\ell+2k-1}.$$

These are the same first- and second-order asymptotics as for tree-child networks with $k$ reticulations: for fixed $k$, networks violating the tree-child condition (or containing multiple edges) are asymptotically negligible. The factor $1-(-1)^n$ reflects the parity constraint on the total number of vertices of a binary network with $k$ reticulations.

## Expansion

The proof extends the *sparsened skeleton decomposition* used for tree-child networks: removing the tree parts of a network with $k$ reticulations leaves one of finitely many small skeleton graphs, and every network is recovered by attaching rooted binary trees along the skeleton's edges. Each skeleton therefore contributes an explicit exponential generating function built from the tree generating function, which has a square-root singularity; singularity analysis shows that the dominant contribution, of order $n^{\,n+2k-1}$, comes only from skeletons yielding tree-child networks, while skeletons with fewer attachment edges (non-tree-child configurations, multiple edges) contribute lower powers of $n$. Relating vertex and leaf labelings gives the leaf-labeled asymptotics.

## Sources

- Marefatollah Mansouri, "Counting general phylogenetic networks", Australasian Journal of Combinatorics 83 (2022), 40–86, <https://ajc.maths.uq.edu.au/v83.p040> (the journal assigns no DOI). Published version of arXiv:2005.14547, cited next; locators there refer to the arXiv version.
- M. Mansouri, "Counting General Phylogenetic networks", arXiv:2005.14547 (2020), Section 1 (definitions and Theorems 1–2) and the skeleton-decomposition and singularity-analysis sections. <https://doi.org/10.48550/arXiv.2005.14547>
