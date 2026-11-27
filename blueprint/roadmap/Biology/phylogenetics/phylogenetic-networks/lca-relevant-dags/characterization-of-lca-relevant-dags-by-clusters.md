# Characterization of lca-relevant DAGs by clusters

**Setting.** Let $G$ be a directed acyclic graph whose set of leaves (out-degree-$0$ vertices) is $X$. Write $u\preceq_G v$ if $v$ is an ancestor of $u$ (there is a directed path from $v$ to $u$, possibly of length $0$), and $C_G(v)=\{x\in X: x\preceq_G v\}$ for the cluster of $v$. For nonempty $A\subseteq X$, $\mathrm{LCA}_G(A)$ is the set of $\preceq_G$-minimal common ancestors of $A$; if it has exactly one element, that element is $\mathrm{lca}_G(A)$.

**Definitions.**
- $v$ is an *LCA vertex* if $v\in\mathrm{LCA}_G(A)$ for some $A\subseteq X$, and an *lca vertex* if $v=\mathrm{lca}_G(A)$ for some $A$. $G$ is *LCA-relevant* (resp. *lca-relevant*) if all its vertices are LCA (resp. lca) vertices.
- $G$ has *(PCC)* if $u,v$ are $\preceq_G$-comparable exactly when $C_G(u)\subseteq C_G(v)$ or $C_G(v)\subseteq C_G(u)$; it has *strong (CL)* if $v=\mathrm{lca}_G(C_G(v))$ for all $v$.
- $G$ is *regular* if $v\mapsto C_G(v)$ is an isomorphism onto the Hasse diagram of its cluster set $\mathfrak{C}_G$.

**Statements.**
1. A vertex $v$ is an LCA (resp. lca) vertex if and only if $v\in\mathrm{LCA}_G(C_G(v))$ (resp. $v=\mathrm{lca}_G(C_G(v))$), and the witnessing set can be taken of size at most $|C_G(v)|$.
2. $G$ is LCA-relevant if and only if no two adjacent vertices have the same cluster.
3. The following are equivalent: (a) $G$ is lca-relevant; (b) $G$ has strong (CL); (c) $G$ satisfies (PCC) and is LCA-relevant; (d) $G$ satisfies (PCC) and distinct vertices have distinct clusters; (e) $C_G(u)\subseteq C_G(v)\iff u\preceq_G v$ for all $u,v$.
4. $G$ has strong (CL) if and only if it is the regular DAG $\mathscr{H}(\mathfrak{C}_G)$ with $\ell\ge 0$ shortcuts added. Consequently, $G$ is regular if and only if it is shortcut-free and lca-relevant.
5. For every set system $\mathfrak{C}$ on $X$ containing $X$ and all singletons and not containing $\emptyset$, there is a phylogenetic lca-relevant DAG $G$ with $\mathfrak{C}_G=\mathfrak{C}$.

## Expansion

If $v\in\mathrm{LCA}_G(A)$ then $A\subseteq C_G(v)$ and every common ancestor of $C_G(v)$ is a common ancestor of $A$, so minimality for $A$ transfers to $C_G(v)$, giving statement 1. A child $u$ of $v$ with $C_G(u)=C_G(v)$ is a common ancestor of $C_G(v)$ below $v$, which is the only obstruction to $v$ being minimal, giving statement 2. Statement 3 follows by combining these with the fact that (PCC) turns comparability of clusters into ancestry. Under strong (CL), ancestry is exactly cluster inclusion, so the DAG is the Hasse diagram of its clusters plus arcs implied by transitivity, i.e. shortcuts; removing them leaves the regular DAG.

## Sources

- Anna Lindeberg and Marc Hellmuth, "Simplifying and Characterizing DAGs and Phylogenetic Networks via Least Common Ancestor Constraints", Bulletin of Mathematical Biology 87 (2025), 44, <https://doi.org/10.1007/s11538-025-01419-z>; numbering as in arXiv:2411.00708: Definitions 3.2 and 3.7, Corollary 3.6, Theorems 4.4, 4.5, 4.6, 4.8 and 4.10, Corollary 4.11.
