# Fitch graphs of horizontal gene transfer and their neighborhood characterization

**Setting.** Let $T$ be a rooted gene tree with leaf set $L$ and $H \subseteq E(T)$ a set of edges marked as horizontal gene transfers (HGT). The directed **Fitch graph** $\mathcal F(T,H)$ has vertex set $L$ and an arc $(x,y)$ whenever the path from $\mathrm{lca}_T(x,y)$ down to $y$ contains an edge of $H$: $y$ is "xenologous" to $x$ because its lineage passed through a transfer since they diverged. A directed graph is a Fitch graph if it equals $\mathcal F(T,H)$ for some $(T,H)$. For a vertex $x$, the closed complementary neighborhood is

$$\overline N[x] = \{y \in L : (x,y) \notin E(G)\}$$

(so $x \in \overline N[x]$), and $\overline{\mathcal N}(G) = \{\overline N[y] : y \in L\}$.

**Theorem.** A directed graph $G$ is a Fitch graph if and only if

1. $\overline{\mathcal N}(G)$ is hierarchy-like: for all $\overline N_1, \overline N_2 \in \overline{\mathcal N}(G)$, $\overline N_1 \cap \overline N_2 \in \{\overline N_1, \overline N_2, \emptyset\}$; and
2. for every $\overline N \in \overline{\mathcal N}(G)$ and every $y \in \overline N$, $|\overline N[y]| \le |\overline N|$.

Fitch graphs are equivalently characterized by eight forbidden induced subgraphs on three vertices (Geiß et al.), so membership is decidable by inspecting vertex triples.

## Expansion

If no transfer edge lies on the path from the root to $x$, every $y$ with a transfer-free path from $\mathrm{lca}(x,y)$ is in $\overline N[x]$; in general the sets $\overline N[x]$ are read off the tree obtained by cutting $T$ at its transfer edges, and sets of this kind are nested or disjoint, which is condition 1. Condition 2 expresses that a gene $y$ inside such a set cannot have strictly more transfer-free partners than the set itself. Conversely, the hierarchy formed by the complementary neighborhoods yields a tree with transfer edges placed above its clusters that realizes $G$. Fitch graphs thus record exactly the information about HGT that is identifiable from pairwise xenology.

## Depends on

- [Orthology graphs of event-labeled gene trees are exactly the cographs](orthology-graphs-of-event-labeled-gene-trees-are-cographs.md)

## Sources

- Marc Hellmuth and Peter F. Stadler, "The Theory of Gene Family Histories", Methods in Molecular Biology (2024), 1–32, <https://doi.org/10.1007/978-1-0716-3838-5_1>; numbering as in arXiv:2304.11826: section on horizontal gene transfer (definition of the directed Fitch graph, closed complementary neighborhoods and Theorem 7).
