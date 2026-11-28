# Closed clustering systems with property (L) characterize level-1 networks

**Setting.** Let $X$ be a finite set and $\mathscr{C}$ a clustering system on $X$ (no empty set, contains $X$ and all singletons). Two sets *overlap* if their intersection is nonempty and neither contains the other. A rooted network $N$ on $X$ is *level-1* if every block (maximal biconnected subgraph) of $N$ contains at most one hybrid vertex other than its own root; a *galled tree* is a level-1 network in which every vertex has in-degree at most $2$. $\mathscr{C}_N$ denotes the set of hardwired clusters of $N$.

**Axioms on $\mathscr{C}$.**

- *Closed:* $A,B\in\mathscr{C}$ and $A\cap B\neq\emptyset$ imply $A\cap B\in\mathscr{C}$.
- *Property (L):* $C_1\cap C_2=C_1\cap C_3$ whenever $C_1\in\mathscr{C}$ overlaps both $C_2\in\mathscr{C}$ and $C_3\in\mathscr{C}$.
- *(N3O):* $\mathscr{C}$ contains no three distinct pairwise overlapping clusters.

**Statements.**

1. The clustering system of every level-1 network satisfies (L), and every clustering system with (L) is a weak hierarchy ($C_1\cap C_2\cap C_3\in\{C_1\cap C_2,C_1\cap C_3,C_2\cap C_3,\emptyset\}$).
2. There is a level-1 network $N$ with $\mathscr{C}_N=\mathscr{C}$ if and only if $\mathscr{C}$ is closed and satisfies (L). In that case the Hasse diagram of $(\mathscr{C},\subseteq)$ is itself a phylogenetic level-1 network whose leaves are the singletons.
3. $\mathscr{C}$ is the clustering system of a galled tree if and only if it is closed and satisfies (L) and (N3O); the Hasse diagram is then a phylogenetic galled tree.
4. There is a binary level-1 network $N$ with $\mathscr{C}_N=\mathscr{C}$ if and only if $\mathscr{C}$ is closed and satisfies (L) and (2-Inc): every cluster has at most two inclusion-maximal proper subclusters and is an inclusion-maximal proper subcluster of at most two clusters.

## Depends on

- [Unique regular and cluster networks of a clustering system](unique-regular-and-cluster-networks-of-a-clustering-system.md)

## Expansion

In a level-1 network two clusters can overlap only if their vertices lie on the two sides of a common cycle, and then their intersection is the cluster of the unique hybrid vertex of that cycle; a third cluster overlapping $C_1$ must also meet it in that same hybrid cluster, which is (L). Closure follows because lca's are unique in a level-1 network. Conversely, given a closed system with (L), one shows that each block of the Hasse diagram is either a single arc or a cycle attached at a cluster $C$ and closing at the intersection of overlapping subclusters of $C$, so each block has at most one hybrid vertex. Three pairwise overlapping clusters force a hybrid vertex with in-degree at least $3$ (the three clusters all contain the shared intersection), so (N3O) is exactly what separates galled trees from general level-1 networks; (2-Inc) bounds the in- and out-degrees in the Hasse diagram by $2$.

## Sources

- Marc Hellmuth, David Schaller and Peter F. Stadler, "Clustering systems of phylogenetic networks", Theory in Biosciences 142 (2023), 301–358, <https://doi.org/10.1007/s12064-023-00398-w>; numbering as in arXiv:2204.13466: Lemma 3.32, Definition of Property (L) and Corollaries 7.17-7.18, Proposition 7.36, Theorem 7.38, Theorem 8.9 and Theorem 8.24.
