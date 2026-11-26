# Treewidth bounds for level-$k$ phylogenetic networks

**Definitions.** A rooted phylogenetic network $N$ is a directed acyclic graph with a single root, leaves bijectively labelled by taxa, and reticulation nodes (in-degree at least two) representing hybridization, recombination, reassortment or horizontal transfer. Its reticulation number is $|E(N)| - |V(N)| + 1$. The **level** of $N$ is the maximum reticulation number of a biconnected component (the number of edges that must be deleted from each biconnected component to make it a tree). The treewidth $\mathrm{tw}(N)$ is that of the underlying undirected graph.

**Facts.** If a biconnected graph $H$ with $m$ edges and $n$ nodes is a minor of $N$, then the level of $N$ is at least $m - n + 1$. All networks of level at most $3$ are planar, there is a non-planar level-$4$ network, and level-$1$ networks are outerplanar.

**Theorem (upper bound).** Every level-$k$ network satisfies

$$\mathrm{tw}(N) \le \frac{k+3}{2}.$$

**Theorem (asymptotic upper bound).** For every $\epsilon > 0$ there is $n_\epsilon$ such that, if every maximal biconnected component of $N$ has reticulation number $k \ge n_\epsilon$, then

$$\mathrm{tw}(N) < \Big(\frac13 + 2\epsilon\Big)k.$$

**Theorem (lower bound).** For large $k$ there are level-$k$ networks with treewidth at least $k/13$; hence the maximum treewidth of level-$k$ networks is $\Theta(k)$.

## Expansion

Treewidth is the maximum over biconnected components, and contracting edges at degree-two nodes does not change the treewidth of a biconnected graph with more than three nodes. After suppressing degree-two nodes, a biconnected component of reticulation number $k$ becomes a graph with maximum degree $3$ and $O(k)$ nodes and edges; a direct elimination argument gives $(k+3)/2$, and the Fomin–Høie bound $\mathrm{tw}(G) \le (1/6 + \epsilon)|V(G)|$ for large cubic graphs, applied to a component with about $2k$ nodes, gives the $(1/3 + 2\epsilon)k$ bound. The lower bound embeds a bounded-degree expander as a network: by the Grohe–Marx inequality $\mathrm{tw}(G) \ge \lfloor x_\alpha(G)(\alpha/2)|V(G)|\rfloor$ in terms of node expansion, its treewidth is linear in its size, hence in $k$. Treewidth-parameterized algorithms on networks are therefore fixed-parameter tractable in the level.

## Sources

- A. Markin, S. Vijendran, O. Eulenstein, "Bounds on the treewidth of level-$k$ rooted phylogenetic networks", arXiv:2411.13380 (2024), Observation 1, Lemma 1 and Corollary 1 (Section 3), Theorems 1–2 (Section 4) and Theorem 3 (Section 5), <https://doi.org/10.48550/arXiv.2411.13380>.
