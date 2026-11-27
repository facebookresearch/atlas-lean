# Normalization versus regularization of phylogenetic networks

**Setting.** A *network* on $X$ is a rooted DAG with leaf set $X$. A vertex $v$ is *visible* if some leaf $x$ has every root-to-$x$ path passing through $v$; $\mathrm{vis}(N)$ is the set of visible vertices and $\overline{\mathrm{vis}}(N)$ its complement. A network is *normal* if it is tree-child and shortcut-free, equivalently shortcut-free with all vertices visible; *strongly normal* if moreover no vertex has exactly one child.

**Normalization.** $\mathrm{cov}(N)$ is the DAG on $\mathrm{vis}(N)$ with an arc $u \to v$ whenever $v \prec_N u$, with shortcuts removed; $\mathrm{norm}(N)$ suppresses the in-degree-1, out-degree-1 vertices of $\mathrm{cov}(N)$. Those suppressed vertices form the set $\mathrm{dvis}(N)$ of *dispensably visible* vertices. Regularization $\mathrm{reg}_i$ is defined via LCA vertices as in the companion article.

**Theorem.**
1. $\mathrm{norm}(N) = \mathrm{cov}(N) \ominus \mathrm{dvis}(N) = (N \ominus \overline{\mathrm{vis}}(N))^- \ominus \mathrm{dvis}(N) = \bigl(N \ominus (\overline{\mathrm{vis}}(N) \cup \mathrm{dvis}(N))\bigr)^-$, and $\mathrm{norm}(N)$ is a normal network on $X$ with vertex set $\mathrm{vis}(N) \setminus \mathrm{dvis}(N)$ whose ancestor order is the restriction of that of $N$.
2. For a normal network $N$, $\mathrm{reg}(N)$ is normal, and $\mathrm{reg}(N) = N$ iff $N$ is regular iff $N$ is strongly normal iff $\mathrm{reg}_i(N) = N$ for all $2 \le i \le |X|$. Moreover a network is strongly normal iff it is normal and $2$-lca-relevant iff it is normal and lca-relevant.
3. For every network $N$ and $i \ge 2$, $\mathrm{norm}(N) = \mathrm{reg}_i(N)$ iff $\mathrm{vis}(N) \setminus \mathrm{dvis}(N)$ equals the set of $k$-lca vertices ($k \le i$) of $N$; this can be tested in polynomial time.

## Depends on

- [Regularization of a DAG via LCA clusters](regularization-of-a-dag-via-lca-clusters.md)

## Expansion

Both constructions delete a vertex set with $\ominus$ and then strip shortcuts; they differ only in which vertices survive: visibility (a vertex is the unique gateway to some leaf) for normalization versus being a unique LCA of a small leaf set for regularization. Writing both as $\ominus$-deletions reduces their comparison to comparing vertex sets, which yields the equivalences in item 3. Neither dominates: there are networks $N_1, N_2$ on three leaves with $\mathrm{reg}(N_1) = \mathrm{norm}(N_2)$ but $\mathrm{norm}(N_1) = \mathrm{reg}(N_2)$ a different tree.

## Sources

- Marc Hellmuth, Anna Lindeberg and Vincent Moulton, "Regularizing and Normalizing DAGs and Phylogenetic Networks", *Bulletin of Mathematical Biology* 88(11) (2026), 209, Theorems 2.4, 3.14, 4.4 and 4.6, Propositions 3.11 and 4.5, Corollaries 4.7 and 4.8, <https://doi.org/10.1007/s11538-026-01783-4> (preprint arXiv:2605.21725).
