# Genus equals vertex cover number for acyclic intersection graphs

**Setting.** An RNA secondary structure on a linear backbone is a *linear chord diagram* $D$: a set of chords $c=(\ell,r)$, $\ell<r$, with distinct endpoints. Two chords $c_1,c_2$ with $\ell_1<\ell_2$ *cross* if $\ell_1<\ell_2<r_1<r_2$, *nest* if $\ell_1<\ell_2<r_2<r_1$, and are *independent* otherwise. The *intersection graph* $G$ of $D$ has the chords as vertices and an edge for each crossing pair. The *genus* of $D$ is

$$
\gamma(D)=\tfrac12\operatorname{rank}_{\mathbb Z_2}\mathrm{Adj}(G),
$$

half the rank over $\mathbb Z_2$ of the adjacency matrix of $G$. The *vertex cover number* $\beta(G)$ is the size of a minimum vertex cover of $G$.

**Theorem.** If the intersection graph $G$ of $D$ is acyclic (a forest), then $\gamma(D)=\beta(G)$.

For general intersection graphs the two invariants differ; for example, for a $k$-crossing, whose intersection graph is the complete graph $K_k$, $\beta(K_k)=k-1$ while $\gamma=\lfloor k/2\rfloor$.

## Expansion

For a forest, the $\mathbb Z_2$-rank of the adjacency matrix equals twice the size of a maximum matching: expanding the determinant of a principal submatrix, the only surviving terms over $\mathbb Z_2$ in an acyclic graph are perfect matchings, and a forest has at most one perfect matching on any vertex set. By König's theorem for bipartite graphs (forests are bipartite) the maximum matching size equals the minimum vertex cover size, so $\gamma=\beta$. The interpretation is that for tree-like pseudoknot configurations the minimum number of chords whose removal makes the structure planar equals the topological genus, linking deletion-based pseudoknot counts to the genus filtration of topological RNA structures.

## Proof depends on

- [Kőnig's theorem for finite bipartite graphs](../../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md)

## Sources

- Rayan Ibrahim, Allison H. Moore, "Methods for Analyzing RNA Pseudoknots via Chord Diagrams and Intersection Graphs", arXiv:2512.19939: Section 2: Definitions 2.1 and 2.5, Theorem 2.6 and Remark 2.7. <https://doi.org/10.48550/arXiv.2512.19939>
