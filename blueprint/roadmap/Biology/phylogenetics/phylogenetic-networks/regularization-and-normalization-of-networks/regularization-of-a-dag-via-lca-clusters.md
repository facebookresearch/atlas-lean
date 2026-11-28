# Regularization of a DAG via LCA clusters

**Setting.** A DAG $G$ on $X$ has leaf set $X$; the *cluster* of a vertex $v$ is $C_G(v) = \{x \in X : x \preceq_G v\}$, and $\mathfrak C(G)$ is the set of clusters. $v$ is a least common ancestor (LCA) of $A \subseteq X$ if it is a $\preceq_G$-minimal common ancestor of $A$; $\mathrm{lca}_G(A)$ is *well-defined* if $A$ has exactly one LCA. $v$ is a *$k$-lca vertex* if $v = \mathrm{lca}_G(A)$ for some $|A| = k$. $G$ is *$i$-lca-relevant* if every vertex is a $k$-lca vertex for some $k \le i$, and *regular* if $v \mapsto C_G(v)$ is an isomorphism from $G$ onto the Hasse diagram $\mathrm{Hasse}(\mathfrak C(G))$. An arc $(u,w)$ is a *shortcut* if another directed $u$–$w$ path exists; $G^-$ deletes all shortcuts. The operator $G \ominus v$ deletes $v$ and joins every parent of $v$ to every child of $v$.

**Definition.** For $i \ge 1$ the *$i$-regularization* is $\mathrm{reg}_i(G) = (G \ominus W_i)^-$, where $W_i$ is the set of vertices that are not $k$-lca vertices for any $k \le i$; the *regularization* is $\mathrm{reg}(G) = \mathrm{reg}_{|X|}(G)$. Let $\mathfrak C_{\mathrm{lca}}(G) = \{C \in \mathfrak C(G) : \mathrm{lca}_G(C) \text{ well-defined}\}$ and $\mathfrak C^{i}_{\mathrm{lca}}(G)$ its members that are the unique inclusion-minimal cluster containing some $A \subseteq X$ with $|A| \le i$.

**Theorem.**
1. A DAG is regular if and only if it is lca-relevant and shortcut-free.
2. $\mathrm{reg}_i(G)$ is an $i$-lca-relevant regular DAG on $X$, and $G$ is regular iff $\mathrm{reg}(G) = G$.
3. $\mathfrak C(\mathrm{reg}_i(G)) = \mathfrak C^{i}_{\mathrm{lca}}(G)$, hence $\mathrm{reg}_i(G) \simeq \mathrm{Hasse}(\mathfrak C^{i}_{\mathrm{lca}}(G))$; in particular $\mathrm{reg}(G) \simeq \mathrm{Hasse}(\mathfrak C_{\mathrm{lca}}(G))$.
4. $\mathrm{reg}(G) \simeq \mathrm{Hasse}(\mathfrak C(G))$ if and only if $G$ has the cluster-lca property: $\mathrm{lca}_G(C_G(v))$ is well-defined for every $v$.
5. $\mathrm{reg}(G)$ is computable in polynomial time, and so is $\mathrm{reg}_i(G)$ for fixed $i$.

## Expansion

Removing a non-lca vertex with $\ominus$ never changes which leaf sets have a unique LCA, so the surviving vertices are exactly the LCAs of the clusters in $\mathfrak C^{i}_{\mathrm{lca}}(G)$; each such LCA is the unique vertex realising its cluster. Deleting shortcuts then leaves precisely the cover relations of the cluster order, which is the Hasse diagram. The cluster-lca property says no cluster is lost in this process, so the regularization reproduces the full cluster system exactly when it holds.

## Sources

- Marc Hellmuth, Anna Lindeberg and Vincent Moulton, "Regularizing and Normalizing DAGs and Phylogenetic Networks", *Bulletin of Mathematical Biology* 88(11) (2026), 209, Definition of regularization (Section 3), Theorems 2.12, 3.3, 3.5 and 3.8, Proposition 3.9, <https://doi.org/10.1007/s11538-026-01783-4> (preprint arXiv:2605.21725).
