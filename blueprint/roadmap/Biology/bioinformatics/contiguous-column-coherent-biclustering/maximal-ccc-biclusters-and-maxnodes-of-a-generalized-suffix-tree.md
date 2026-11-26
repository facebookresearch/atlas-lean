# Maximal CCC-biclusters correspond to MaxNodes of a generalized suffix tree

**Definitions.** Let $A$ be an $|R|\times|C|$ matrix over a finite alphabet $\Sigma$ (genes by time points, after discretization). A *CCC-bicluster* $A_{IJ}$ is a set of rows $I$ and a set of contiguous columns $J = \{r, r+1,\dots,s\}$ such that $A_{ij} = A_{lj}$ for all $i,l \in I$, $j \in J$; it defines the common string $S$ of the rows of $I$ on $J$. It is *row-maximal* if no row can be added, *left-* (*right-*) *maximal* if $S$ cannot be extended by one column on the left (right) without changing $I$, and *maximal* if no other CCC-bicluster properly contains it. Every maximal CCC-bicluster is row-, left- and right-maximal.

Replace each symbol $A_{ij}$ by the pair $(A_{ij}, j) \in \Sigma \times \{1,\dots,|C|\}$ and build the generalized suffix tree $\mathcal{T}$ of the $|R|$ transformed rows. An internal node $v$ of $\mathcal{T}$ is a *MaxNode* if it has no incoming suffix links, or if every node $u$ with a suffix link to $v$ has fewer leaves in its subtree than $v$.

**Theorem.** (a) Right- and row-maximal CCC-biclusters with at least two rows are in bijection with internal nodes of $\mathcal{T}$: the rows are the string terminators below $v$, and the columns are read off the string depth of $v$ and the column index in the first symbol of its path label. (b) Such a node gives a left-maximal bicluster if and only if it is a MaxNode. Consequently, maximal CCC-biclusters with at least two rows are in bijection with MaxNodes, and all of them can be reported in $O(|R||C|)$ time.

## Expansion

Appending column indices to symbols forces any shared substring of two transformed rows to occur at the same columns, so a common path label is exactly a common expression pattern on a fixed column interval; branching at $v$ means the pattern cannot be extended to the right without losing rows. A suffix link from $u$ to $v$ means the label of $v$ is the label of $u$ with its first symbol removed. If such a $u$ has as many leaves as $v$, the pattern of $v$ extends one column to the left with the same rows, so $v$ is not left-maximal; if all such $u$ have fewer leaves, no left extension keeps the row set. Ukkonen's algorithm builds $\mathcal{T}$ in linear time, and one traversal marks the MaxNodes.

## Sources

- Madeira SC, Oliveira AL, "A polynomial time biclustering algorithm for finding approximate expression patterns in gene expression time series", Algorithms Mol Biol (2009), Definitions 1–7, Lemmas 1–3 and Theorem 1, <https://doi.org/10.1186/1748-7188-4-8>, PMCID PMC2709627.
