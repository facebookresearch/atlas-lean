# Auxiliary-graph criterion for time-consistent reconciliation

**Setting.** Let $\mu$ be a reconciliation map from an event-labeled gene tree $(T;t,\sigma)$, $T=(V,E)$, to a species tree $S=(W,F)$ (labels: $\bullet$ speciation, $\square$ duplication, $\triangle$ transfer, $\odot$ leaf; $T_{\bar E}$ is $T$ with transfer edges removed). A time map for a rooted tree is $\tau:V\to\mathbb R$ with $x\prec y\Rightarrow\tau(x)>\tau(y)$ (descendants are later). $\mu$ is **time-consistent** if there are time maps $\tau_T,\tau_S$ with

- (C1) $\tau_T(u)=\tau_S(\mu(u))$ whenever $t(u)\in\{\bullet,\odot\}$;
- (C2) $\tau_S(y)>\tau_T(u)>\tau_S(x)$ whenever $t(u)\in\{\square,\triangle\}$ and $\mu(u)=(x,y)\in F$.

**Auxiliary graph.** On vertex set $W\cup V$ put directed edges:
(A1) for $(u,v)\in E$, an edge $u'\to v'$, where $u'=\mu(u)$ if $t(u)\in\{\bullet,\odot\}$ and $u'=u$ otherwise (same for $v'$);
(A2) every edge $(x,y)\in F$;
(A3) $u\to\operatorname{lca}_S(\sigma_{T_{\bar E}}(u))$ for every $u$ with $t(u)\in\{\square,\triangle\}$;
(A4) $\operatorname{lca}_S(\sigma_{T_{\bar E}}(u)\cup\sigma_{T_{\bar E}}(v))\to u$ for every transfer edge $(u,v)$;
(A5) $x\to u$ and $u\to y$ for every $u$ with $t(u)\in\{\square,\triangle\}$ and $\mu(u)=(x,y)$.
Let $A_1$ use (A1), (A2), (A5) and $A_2$ use (A1)–(A4).

**Theorem.**

1. $\mu$ is time-consistent if and only if $A_1$ is a directed acyclic graph.
2. Some time-consistent reconciliation map (possibly different from $\mu$) from $(T;t,\sigma)$ to $S$ exists if and only if $A_2$ is a directed acyclic graph.
3. Given a species tree $S$ for $(T;t,\sigma)$, one can decide whether a time-consistent reconciliation map exists, and construct one if it does, in $O(|V|\log|W|)$ time.

## Expansion

A topological order of a DAG is exactly a time map on the union of the two trees, so acyclicity is equivalent to the existence of simultaneous dates. For (1), (C1) collapses each speciation or leaf of $T$ onto its image in $S$ (edges (A1)), and (C2) forces a duplication or transfer to lie strictly between the endpoints of its image edge (edges (A5)). For (2), the edge placement of duplications and transfers is left free; (A3) says such an event precedes the lca of the species below it, and (A4) says the donor of a transfer precedes the lca of everything the donor and recipient lineages cover, which is the "no transfer into the past" condition. $A_2$ does not depend on where $\mu$ places non-speciation vertices, so any one reconciliation decides existence. The algorithm computes all $\operatorname{lca}_S(\sigma_{T_{\bar E}}(u))$ by a depth-first pass with $O(\log|W|)$ pairwise lca queries, builds $A_2$, tests acyclicity by depth-first search, and slides each duplication or transfer to an edge compatible with the resulting order.

## Depends on

- [Reconciliation maps for event-labeled gene trees](reconciliation-map-for-event-labeled-gene-trees.md)

## Sources

- N. Nøjgaard, M. Geiß, D. Merkle, P. F. Stadler, N. Wieseke, M. Hellmuth, "Time-consistent reconciliation maps and forbidden time travel", *Algorithms for Molecular Biology* 13:2 (2018), Definitions 3, 4 and 6, Theorems 2, 4, 5 and 6, Lemma 3, <https://doi.org/10.1186/s13015-018-0121-8>, PMCID: PMC5800358.
