# Maximum agreement graphs and the agreement distance

**Networks.** Let $X=\{1,\dots,n\}$. An unrooted binary phylogenetic network $N$ on $X$ is a connected undirected multigraph whose leaves are bijectively labelled by $X$ and whose non-leaf vertices have degree three; it is *proper* if every cut-edge separates two labelled leaves. Let $\mathcal U_n$ be the set of proper such networks. $N$ is in *tier* $r$ if $r=|E|-(|V|-1)$, its cyclomatic number. A *sprout* of a graph is an unlabelled vertex of degree one.

**Agreement embeddings.** A graph $G$ with $n$ vertices labelled bijectively by $X$ has an *agreement embedding* into $N$ if subdivisions of its components embed into pairwise edge-disjoint subgraphs of $N$ such that (i) the embedded components cover every edge of $N$, (ii) at most two vertices of $G$ map to the same vertex of $N$, and if two do, one is a sprout and the other a labelled isolated vertex, and (iii) each labelled vertex of $N$ is the image of the vertex of $G$ with the same label.

**Agreement graph.** Let $N,N'\in\mathcal U_n$ be in tiers $r\le r'$ and $l=r'-r$. A graph $G$ with components $S_1,\dots,S_m$ (no sprouts) and $E_1,\dots,E_k$ (each a single edge on two unlabelled vertices) is an *agreement graph* of $N$ and $N'$ if $G$ minus $E_{k-l+1},\dots,E_k$ has an agreement embedding into $N$ and $G$ has an agreement embedding into $N'$. The $S_i$ are *agreement subgraphs*, the $E_j$ *disagreement edges*. A *maximum agreement graph* (MAG) has the fewest disagreement edges, and the *agreement distance* is

$$d_{\mathrm{AD}}(N,N')=k,$$

the number of disagreement edges of a MAG (equivalently, half its number of sprouts). For two trees a MAG is a maximum agreement forest together with its connecting disagreement edges.

**Theorem.**
1. $d_{\mathrm{AD}}$ is a metric on $\mathcal U_n$.
2. On unrooted binary phylogenetic trees, $d_{\mathrm{AD}}$ equals the TBR-distance.
3. Computing $d_{\mathrm{AD}}$ on $\mathcal U_n$ is NP-hard.

## Expansion

Every MAG admits an *ordered* agreement embedding (disagreement edges can be ordered so that the first $m-1$ successively join distinct agreement components and the rest attach only to earlier pieces), proved by recolouring the edges of $N$ covered by disagreement edges and peeling off paths between black components. Symmetry, non-negativity and identity of indiscernibles are immediate; for the triangle inequality, fix ordered embeddings of MAGs $G'$ of $(N,N')$ and $G''$ of $(N',N'')$ into the common network $N'$ and overlay them, cutting agreement subgraphs of one at the attachment points of the other, which produces an agreement graph of $N$ and $N''$ with at most $k'+k''$ disagreement edges. On trees each agreement subgraph is a tree, so a MAG is a maximum agreement forest, whose number of components minus one is the TBR-distance by the Allen–Steel theorem; NP-hardness of the tree TBR-distance then transfers.

## Sources

- J. Klawitter, "The agreement distance of unrooted phylogenetic networks", Discrete Mathematics & Theoretical Computer Science 22(1) (2020); arXiv:1908.08183, <https://doi.org/10.48550/arXiv.1908.08183>. Section 2 (Observation 2.1), Section 3 (Lemma 3.1, Theorem 3.2, Proposition 3.3, Corollary 3.4).
