# Corrected two-colour characterization of best match graphs

**Setting.** Notation as for colored best match graphs: $(G, \sigma)$ is a vertex-coloured digraph on $L$, an $n$-cBMG is a digraph of the form $G(T, \sigma)$ for a leaf-coloured rooted tree, $(G_{st}, \sigma_{st})$ is the subgraph induced by the vertices of colours $s$ and $t$, and $R(G, \sigma)$ is the set of informative triples $ab \mid b'$ ($\sigma(a) \ne \sigma(b) = \sigma(b')$, $ab \in E(G)$, $ab' \notin E(G)$). For each pair of colours whose induced subgraph is a 2-cBMG, let $(T^{*}_{st}, \sigma_{st})$ be its least resolved tree and put

$$\mathcal{R} := \bigcup_{s, t \in S} r(T^{*}_{st}),$$

the union of all triples displayed by these trees, with $\mathrm{Aho}(\mathcal{R})$ built on the full leaf set $L = V(G)$.

**Sink-freeness.** Every cBMG has the property that each vertex $x$ has an out-arc to at least one vertex of every colour other than $\sigma(x)$. For properly 2-coloured digraphs this is the condition (N4) that the out-neighbourhood of every class (set of vertices with identical in- and out-neighbourhoods) is non-empty. It must be imposed explicitly as a hypothesis in the 2-colour least-resolved-tree construction, and an algorithm building that tree must check it, which costs $O(|E|)$.

**Theorem (corrected $n$-colour characterization).** A connected coloured digraph $(G, \sigma)$ is an $n$-cBMG if and only if

1. every 2-coloured induced subgraph $(G_{st}, \sigma_{st})$ is a 2-cBMG,
2. the triple set $\mathcal{R}$ is consistent, and
3. $G(\mathrm{Aho}(\mathcal{R}), \sigma) = (G, \sigma)$.

In that case $(\mathrm{Aho}(\mathcal{R}), \sigma)$ is the unique least resolved tree explaining $(G, \sigma)$.

**Conditions 1 and 2 are not sufficient.** There is a 3-coloured digraph on vertices $a_1, a_2, b, c_1, c_2$ whose three 2-coloured induced subgraphs are 2-cBMGs with consistent triple union

$$\mathcal{R} = \{a_1 b \mid a_2,\ a_1 c_1 \mid a_2,\ a_1 c_1 \mid c_2,\ a_2 c_2 \mid a_1,\ a_2 c_2 \mid c_1\},$$

yet $G(\mathrm{Aho}(\mathcal{R}), \sigma)$ lacks the arc $bc_2$ of $(G, \sigma)$, so $(G, \sigma)$ is not a 3-cBMG. The reason is that $\mathrm{Aho}(\mathcal{R})$ can display triples present in none of the 2-coloured trees.

**Supporting propositions.**

- If $(G, \sigma)$ is an $n$-cBMG, then $\mathrm{Aho}(R(G, \sigma)) = \mathrm{Aho}(\mathcal{R})$.
- If $(G, \sigma)$ is properly $n$-coloured and all its 2-coloured induced subgraphs are 2-cBMGs, then consistency of $R(G, \sigma)$ implies $G(\mathrm{Aho}(R(G, \sigma)), \sigma) \subseteq (G, \sigma)$, and consistency of $\mathcal{R}$ implies $G(\mathrm{Aho}(\mathcal{R}), \sigma) \subseteq (G, \sigma)$. So under conditions 1 and 2 the Aho tree can only lose arcs, never create spurious ones, and condition 3 detects exactly the missing arcs.

## Depends on

- [The Aho tree of informative triples characterizes best match graphs](aho-tree-of-informative-triples-characterizes-best-match-graphs.md)
## Expansion

Condition 3 is clearly sufficient, and conditions 1–2 are needed for $\mathcal{R}$ and its Aho tree to exist. Necessity of condition 3 follows from the informative-triple characterization. Each informative triple involves only two colours, so $R(G, \sigma) \subseteq \mathcal{R}$, and for an $n$-cBMG the same connected-component argument used for $R(G, \sigma)$ shows that BUILD on $\mathcal{R}$ splits the leaves exactly as the least resolved tree does. Every triple of $\mathcal{R}$ is displayed by that tree, so no Aho-graph edge crosses a child cluster. The subgraph statements use sink-freeness. If the Aho tree had an arc $ab$ missing from $G$, the 2-cBMG on colours $\sigma(a), \sigma(b)$ supplies some $b'$ of colour $\sigma(b)$ with $ab' \in E(G)$. Then $ab' \mid b$ is informative and displayed by the Aho tree, which contradicts $ab$ being a best match there. The original statement of the theorem omitted condition 3 and the sink-free hypothesis, and this note restores both. The recognition algorithm becomes simpler: build the Aho tree of the informative triples and compare graphs, without requiring a connected input.

## Sources

- D. Schaller, M. Geiß, E. Chávez, M. González Laffitte, A. López Sánchez, B. M. R. Stadler, D. I. Valdivia, M. Hellmuth, M. Hernández Rosales, P. F. Stadler, "Corrigendum to 'Best match graphs'", Journal of Mathematical Biology 82 (2021) 47, property (N4), corrected Theorem 9, Fig. 1, Propositions 2 and 3, <https://doi.org/10.1007/s00285-021-01601-6> (PMC8021527).
- M. Geiß et al., "Best match graphs", Journal of Mathematical Biology 78 (2019) 2015–2057, Lemmas 9 and 11, Theorems 4 and 9 (as corrected), <https://doi.org/10.1007/s00285-019-01332-9>.
