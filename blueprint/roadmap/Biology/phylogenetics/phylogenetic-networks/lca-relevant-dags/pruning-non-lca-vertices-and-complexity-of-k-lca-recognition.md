# Pruning non-lca vertices and complexity of k-lca recognition

**Setting.** $G=(V,E)$ is a DAG with leaf set $X$; clusters $C_G(v)$, the ancestor order $\preceq_G$, $\mathrm{LCA}_G(A)$ and $\mathrm{lca}_G(A)$ are as in the characterization of lca-relevant DAGs. For $k\ge 1$, $v$ is a *$k$-lca vertex* if $v=\mathrm{lca}_G(A)$ for some $A\subseteq X$ with $|A|=k$ ($k$-LCA analogously), and for $\mathscr{I}\subseteq\{1,\dots,|X|\}$ with $1\in\mathscr{I}$, $G$ is $\mathscr{I}$-lca-relevant if every vertex is a $k$-lca vertex for some $k\in\mathscr{I}$.

**The $\ominus$ operator.** For $v\in V$, $G\ominus v$ deletes $v$ and adds an arc $(p,q)$ for every parent $p$ and child $q$ of $v$; for $W=\{w_1,\dots,w_\ell\}$, $G\ominus W$ deletes them one after another.

**Statements.**
1. *(Pruning is safe.)* If $W$ is a nonempty set of vertices none of which is an $\mathscr{I}$-lca vertex, then $G\ominus W$ is a DAG on the same leaf set, uses only vertices of $G$, preserves the ancestor relation among its vertices, introduces no new clusters and has the same unique least common ancestors as $G$ for all subsets of $X$. If $W$ contains all non-$\mathscr{I}$-lca vertices, $G\ominus W$ is $\mathscr{I}$-lca-relevant. The analogous statement holds for LCA vertices, where moreover all sets $\mathrm{LCA}_G(A)$ are preserved.
2. *(Canonical result under (PCC).)* If $G$ satisfies (PCC) or (CL) and $W$ is the set of vertices that are not lca vertices for any $k$, then $W$ is also the set of non-LCA vertices, it is the unique smallest set whose removal gives an lca-relevant DAG with the preservation properties of statement 1, $\mathfrak{C}_{G\ominus W}=\mathfrak{C}_G$, and removing the shortcuts of $G\ominus W$ gives the Hasse diagram of $\mathfrak{C}_G$. If $\mathfrak{C}_G$ is a hierarchy, the result is the unique phylogenetic tree with that cluster set.
3. *(Hardness for fixed sizes.)* Given a DAG $G$, a vertex $v$ and an integer $1<k\le |X|$, deciding whether $v$ is a $k$-lca vertex, and likewise whether it is a $k$-LCA vertex, is NP-complete, even when $G$ is a regular network. Deciding whether $G$ is $\mathscr{I}$-LCA-relevant or $\mathscr{I}$-lca-relevant for a given $\mathscr{I}$ is also NP-complete.
4. *(Tractable case.)* Without the size restriction, membership $v\in\mathrm{LCA}_G(A)$ and $v=\mathrm{lca}_G(A)$ can be tested in $O((|V|+|E|)|A|)$ time, so lca- and LCA-relevance are decidable in polynomial time. If $\mathfrak{C}_G$ has no three pairwise overlapping clusters (N3O), the $\mathscr{I}$-versions are also polynomial.

## Depends on

- [Characterization of lca-relevant DAGs by clusters](characterization-of-lca-relevant-dags-by-clusters.md)

## Expansion

Removing a vertex with $\ominus$ keeps every path through it, so ancestry among surviving vertices and all clusters are unchanged; a vertex that is not the lca of anything can be removed without changing any lca, which gives statement 1 by induction over $W$. Under (PCC) every surviving vertex is lca of its own cluster and clusters are distinct, so the result is the Hasse diagram up to shortcuts. Hardness is a reduction from Vertex Cover: a gadget network encodes the graph so that a fixed vertex is the lca of some $k$-subset of leaves exactly when a small vertex cover exists. Under (N3O) the number of candidate minimal subsets is polynomially bounded, which restores tractability.

## Sources

- Anna Lindeberg and Marc Hellmuth, "Simplifying and Characterizing DAGs and Phylogenetic Networks via Least Common Ancestor Constraints", Bulletin of Mathematical Biology 87 (2025), 44, <https://doi.org/10.1007/s11538-025-01419-z>; numbering as in arXiv:2411.00708: Definition 5.2, Proposition 3.11, Corollary 3.12, Theorems 5.5 and 5.8, Corollary 6.3, Theorems 7.4, 7.5 and 7.12.
