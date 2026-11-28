# Spanning edge betweenness via the matrix-tree theorem

**Setting.** Let $G=(V,E)$ be a connected, undirected, simple graph with $n=|V|$ vertices and edge weights $w:E\to\mathbb R$; in phylogenetic and epidemiological typing, vertices are isolates and $w$ is an allelic distance. Let $\tau_G$ be the number of minimum spanning trees (MSTs) of $G$ and $\tau_G(e)$ the number of MSTs that contain an edge $e$. The *spanning edge betweenness* of $e$ is

$$\delta_G(e)=\frac{\tau_G(e)}{\tau_G}\in[0,1],$$

the fraction of equally optimal MSTs in which $e$ appears, a support value for $e$ analogous to a bootstrap proportion.

Let $L$ be the (unweighted) Laplacian of $G$, $L_{(i)}$ the matrix $L$ with row and column $i$ deleted, and $L_{(ij)}$ the matrix $L$ with rows and columns $i$ and $j$ deleted. By the [matrix-tree theorem](../../../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree-lap-matrix.md), $\det L_{(i)}$ is the number of spanning trees of $G$ for every $i$.

**Theorem (spanning trees through an edge).** For $e=(i,j)\in E$, $\det L_{(ij)}$ equals the number of spanning trees of $G$ that contain $e$.

**Weighted case (Lemmas 1-2).** Process the edges in increasing weight as in Kruskal's algorithm. At each distinct weight $c$, let $H$ be the graph whose vertices are the components of the forest built from edges of weight $<c$, with all edges of weight $c$ added. Then $\tau_G=\prod_C\tau_C$ over the connected components $C$ of these graphs $H$ across all weight levels, and for an edge $e$ of weight $c$ lying in component $C$, $\delta_G(e)=\delta_C(e)$. Hence every $\delta_G(e)$ is a ratio of two determinants of contracted Laplacians.

## Proof depends on

- [Matrix-tree theorem for principal minors of the Laplacian](../../../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree-lap-matrix.md)

## Expansion

For the theorem, deleting $e$ gives $G'$ with Laplacian $L'$, and the spanning trees containing $e$ number $\det L_{(i)}-\det L'_{(i)}$. Since $L_{(i)}$ and $L'_{(i)}$ differ only in the $(j,j)$ entry, by exactly $1$, cofactor expansion along row $j$ gives $\det L_{(i)}=\det L'_{(i)}+\det L_{(ij)}$. For the weighted case, two MSTs can differ only by exchanging edges of equal weight, and an edge of weight $c$ can only be exchanged with another edge of weight $c$ that closes a cycle in $H$; so the choices at different weight levels and in different components are independent, and multiplicativity follows.

## Sources

- Teixeira AS, Monteiro PT, Carriço JA, Ramirez M, Francisco AP, "Not seeing the forest for the trees: size of the minimum spanning trees (MSTs) forest and branch significance in MST-based phylogenetic analysis", PLoS One 2015 Mar 23;10(3):e0119315, Equation (1), Theorems 1-2, Lemmas 1-2 and algorithm SEB, <https://doi.org/10.1371/journal.pone.0119315>, PMCID PMC4370493.
